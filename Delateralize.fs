module Delateralize

module Q = Query

// C(q1, x.q2) := for x :- q1, #y :- q2 do {(x,#y)}
let graph_query (q1,ty1) x (q2,ty2) =
    let y = Var.fresh_raw_var () in
    Q.For ([(x, q1); (y, q2)], 
        Q.Singleton (
            Q.Record (Q.box_pair (Q.Var (x,ty1)) (Q.Var (y,ty2)))))

// XXX: what if we have y :- I(q3) instead?
// for x :- q2, y :- ID(q3) do q1
//  ~> for x :- N, p :- ID(C(N,x.P)) where x = p.1 do ([y]M) p.2
let prom_delateralize q1 x (q2,ty2) y (q3,ty3) =
    let p = Var.fresh_raw_var () in
    // FIXME types of 1 and 2 should be RecordType ty2, RecordType ty3
    let typ = [("1",());("2",())] |> Map.ofList in
    let vp = Q.Var (p,typ) in
    let eq_query a b = Q.Apply (Q.Primitive "==", [a;b]) in
    Q.For ([(x,q2); (p, Q.Prom (Q.Dedup (graph_query (q2,ty2) x (q3,ty3))))],
        Q.If (eq_query (Q.Var (x,ty2)) (Q.Project (vp, "1")),
            Q.Apply (Q.Closure (([y], q1), Map.empty),
                [Q.Project (vp,"2")]),
            Q.nil))
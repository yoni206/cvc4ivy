;Let (V,E) be a directed forest. That is, it is a acyclic and every vertex has outdegree 1.
;Then, let E* denote the reflexive transitive closure of E. The following holds:
;forall X. E*(X,X)
;forall X,Y,Z. E*(X,Y) & E*(Y,Z) -> E*(X,Z)
;forall X,Y. E*(X,Y) & E*(Y,X) -> X=Y 
;forall X,Y,Z. E*(X,Y) & E*(X,Z) -> E*(Y,Z) | E*(Z,Y)

(set-logic ALL)
(define-sort Node () Int)
(define-sort NodeSet () (Set (Tuple Node)))
(define-sort Edge () (Tuple Node Node))
(define-sort EdgeSet () (Set Edge))
(define-sort PreGraph () (Tuple NodeSet EdgeSet))

(define-fun nodes ((g PreGraph)) NodeSet ((_ tupSel 0) g))
(define-fun edges ((g PreGraph)) EdgeSet ((_ tupSel 1) g))
(define-fun directed_neighbor ((g PreGraph) (v Node) (u Node)) Bool (member (mkTuple v u) (edges g)))
(define-fun node_in_pregraph ((v Node) (g PreGraph)) Bool (member (mkTuple v) (nodes g) )) 
(define-fun union_pregraph ((g1 PreGraph) (g2 PreGraph)) PreGraph (mkTuple (union (nodes g1) (nodes g2)) (union (edges g1) (edges g2))))
(define-fun tc_pregraph ((g PreGraph)) PreGraph (mkTuple (nodes g) (tclosure (edges g))) )
(define-fun is_identity_pregraph ((g PreGraph)) Bool (forall ((v Node) (u Node)) (= (directed_neighbor g v u) (= v u))))
(declare-fun identity_graph_over (NodeSet) PreGraph)
(define-fun rtc_pregraph ((g PreGraph)) PreGraph (union_pregraph g (identity_graph_over (nodes g))))


(define-fun graph ((g PreGraph)) Bool (subset (edges g) (product (nodes g) (nodes g)))) 
;out degree at least one
(define-fun total ((g PreGraph)) Bool (forall ((v Node)) (=> (node_in_pregraph v g) (exists ((u Node)) (and (node_in_pregraph u g) (directed_neighbor g v u))))))
;out degree at most one
(define-fun functional ((g PreGraph)) Bool (forall ((v Node) (u1 Node) (u2 Node)) (=> (and (node_in_pregraph v g) (node_in_pregraph u1 g) (node_in_pregraph u2 g) (directed_neighbor g v u1) (directed_neighbor g v u2)) (= u1 u2))))
(define-fun acyclic ((g PreGraph)) Bool (forall ((v Node)) (=> (node_in_pregraph v g) (not (directed_neighbor (tc_pregraph g) v v)))))

(declare-fun g () PreGraph)
(assert (graph g))
(assert (graph (rtc_pregraph g)))
(assert (and (is_identity_pregraph (identity_graph_over (nodes g)) ) (graph (identity_graph_over (nodes g)))))

(define-fun ax1 () Bool (forall ((v Node)) (directed_neighbor (rtc_pregraph g) v v)))

(push)
(assert (not ax1))
(check-sat)
(pop)

(push)
(assert ax1)
(check-sat)
(pop)

(set-logic ALL)

;sorts
(declare-sort node 0)
(define-sort id () Int)
(define-sort node_relation () (Set (Tuple node node)))
(define-sort pending_relation () (Set (Tuple id node)))

;functions and constants
(declare-fun idn (node) id)
(declare-fun r () node_relation ) ;the ring
(define-fun S () (Set (Tuple node)) (as univset (Set (Tuple node))) ) ;the set of nodes
(define-fun SxS () node_relation (product S S)) ;S^2
(declare-fun next (node) node) ;the next function

;being a ring
(define-fun is_a_rel_over_s ((r node_relation) ) Bool (subset r SxS))
(define-fun is_functional ((r node_relation)) Bool (forall ((x node) (y node) (z node)) (=> (and (member (mkTuple x y) r) (member (mkTuple x z) r)) (= y z))))
(define-fun no_loops ((r node_relation)) Bool (forall ((x node)) (not (member (mkTuple x x) r))))
(define-fun is_total ((r node_relation) ) Bool (forall ((x node)) (=> (member (mkTuple x) S) (exists ((y node)) (and (member (mkTuple y) S) (member (mkTuple x y) r) )))))
(define-fun is_ring ((r node_relation) ) Bool (and (is_a_rel_over_s r) (is_functional r) (no_loops r) (is_total r) (= (tclosure r) (product S S))))

;assertions about the ring and the next function
(assert (is_ring r ))
(assert (forall ((n node)) (member (mkTuple n (next n)) r)))

;transition system
(define-fun initial_state ((l (Set node)) (p pending_relation)) Bool (and (= l (as emptyset (Set node))) (= p (as emptyset pending_relation))))
(define-fun transition_l ((l (Set node)) (ll (Set node)) (p pending_relation) (pp pending_relation) ) Bool (forall ((n node)) (= (or (member n l) (member (mkTuple (idn n) n) p))  (member n ll)) ))
(define-fun transition_p ((l (Set node)) (ll (Set node)) (p pending_relation) (pp pending_relation) ) Bool (forall ((n node) (m id)) (= (or (= m (idn n)) (member (mkTuple m (next n)) p) (and  (member (mkTuple m n) p) (< (idn n) m))) (member (mkTuple m (next n)) pp)) ))
(define-fun transition ((l (Set node)) (ll (Set node)) (p pending_relation) (pp pending_relation)) Bool (and 
(transition_l l ll p pp) (transition_p l ll p pp) 
) )
(define-fun safety ((l (Set node)) (p pending_relation)) Bool (forall ((x node) (y node)) (=> (and (member x l) (member y l)) (= x y))))

;bmc
(declare-fun leader0 () (Set node))
(declare-fun pending0 () (Set (Tuple id node)))
(assert (initial_state leader0 pending0))

(declare-fun leader1 () (Set node))
(declare-fun pending1 () (Set (Tuple id node)))
(assert (transition leader0 leader1 pending0 pending1))

(declare-fun leader2 () (Set node))
(declare-fun pending2 () (Set (Tuple id node)))
;(assert (transition leader1 leader2 pending1 pending2))

(declare-fun leader3 () (Set node))
(declare-fun pending3 () (Set (Tuple id node)))
;(assert (transition leader2 leader3 pending2 pending3))

;(assert (not (safety leader3 pending3)))

(check-sat)
;(get-value (leader0 pending0 leader1 pending1 leader2 pending2 leader3 pending3))

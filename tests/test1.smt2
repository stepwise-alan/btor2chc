(set-logic HORN)
(declare-fun Inv ((_ BitVec 32) (_ BitVec 32)) Bool)
(assert (forall ((s_4 (_ BitVec 32)) (s_5 (_ BitVec 32))) (=> (and (= s_4 #x00000000) (= s_5 #x00000000)) (Inv s_4 s_5))))
(assert (forall ((s_4 (_ BitVec 32)) (s_5 (_ BitVec 32)) (i_3 Bool)) (=> (Inv s_4 s_5) (Inv (ite i_3 s_4 (bvadd s_4 #x00000001)) (ite (not i_3) s_5 (bvadd s_5 #x00000001))))))
(assert (forall ((s_4 (_ BitVec 32)) (s_5 (_ BitVec 32))) (=> (and (Inv s_4 s_5) (and (= s_4 #x00000003) (= s_5 #x00000003))) false)))
(check-sat)
(get-model)
(exit)

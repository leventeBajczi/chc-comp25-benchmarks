(set-logic HORN)


(declare-fun |step_lturn| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |lturn| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |combined_lturn| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |CHC_COMP_FALSE| ( ) Bool)
(declare-fun |combined_lturn__bar| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |step_lturn__bar| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) ) 
    (=>
      (and
        (and (>= (+ (* (- 1) N) K) 1)
     (>= (+ (* (- 1) N) I) 2)
     (>= (+ (* (- 1) N) G) 0)
     (>= (+ (* (- 1) N) F) 2)
     (>= (+ (* (- 1) N) B) (- 1))
     (>= (+ (* (- 1) N) A) 0)
     (>= (+ (* (- 1) N) J) 0)
     (>= (+ (* (- 1) L) K) (- 1))
     (>= (+ (* (- 1) L) J) (- 2))
     (>= (+ (* (- 1) K) J) (- 1))
     (>= (+ (* (- 1) I) F) 0)
     (>= (+ (* (- 1) H) L) 3)
     (>= (+ (* (- 1) H) K) 3)
     (>= (+ (* (- 1) H) I) 4)
     (>= (+ (* (- 1) H) G) 2)
     (>= (+ (* (- 1) H) F) 4)
     (>= (+ (* (- 1) H) B) 1)
     (>= (+ (* (- 1) H) J) 2)
     (>= (+ (* (- 1) G) L) 1)
     (>= (+ (* (- 1) G) K) 1)
     (>= (+ (* (- 1) G) J) 0)
     (>= (+ (* (- 1) E) N) 1)
     (>= (+ (* (- 1) E) L) 2)
     (>= (+ (* (- 1) E) K) 2)
     (>= (+ (* (- 1) E) I) 3)
     (>= (+ (* (- 1) E) G) 1)
     (>= (+ (* (- 1) E) F) 3)
     (>= (+ (* (- 1) E) B) 0)
     (>= (+ (* (- 1) E) A) 1)
     (>= (+ (* (- 1) E) J) 1)
     (>= (+ (* (- 1) D) I) (- 1))
     (>= (+ (* (- 1) D) F) (- 1))
     (>= (+ (* (- 1) C) (* (- 1) H)) (- 2))
     (>= (+ (* (- 1) C) N) 2)
     (>= (+ (* (- 1) C) L) 3)
     (>= (+ (* (- 1) C) K) 3)
     (>= (+ (* (- 1) C) I) 4)
     (>= (+ (* (- 1) C) H) 0)
     (>= (+ (* (- 1) C) G) 2)
     (>= (+ (* (- 1) C) F) 4)
     (>= (+ (* (- 1) C) B) 1)
     (>= (+ (* (- 1) C) A) 2)
     (>= (+ (* (- 1) C) J) 2)
     (>= (+ (* (- 1) B) L) 2)
     (>= (+ (* (- 1) B) K) 2)
     (>= (+ (* (- 1) B) G) 1)
     (>= (+ (* (- 1) B) F) 3)
     (>= (+ (* (- 1) B) J) 1)
     (>= (+ (* (- 1) A) L) 1)
     (>= (+ (* (- 1) A) K) 1)
     (>= (+ (* (- 1) A) I) 2)
     (>= (+ (* (- 1) A) G) 0)
     (>= (+ (* (- 1) A) F) 2)
     (>= (+ (* (- 1) A) B) (- 1))
     (>= (+ (* (- 1) A) J) 0)
     (>= (+ N (* (- 1) H)) 2)
     (>= (+ N (* (- 1) G)) 0)
     (>= (+ N (* (- 1) B)) 1)
     (>= (+ N (* (- 1) A)) 0)
     (>= (+ N L) 7)
     (>= (+ N K) 7)
     (>= (+ N I) 8)
     (>= (+ N H) 4)
     (>= (+ N G) 6)
     (>= (+ N F) 8)
     (>= (+ N B) 5)
     (>= (+ N A) 6)
     (>= (+ N J) 6)
     (>= (+ L (* (- 1) K)) 0)
     (>= (+ L (* (- 1) J)) 1)
     (>= (+ L K) 8)
     (>= (+ L J) 7)
     (>= (+ K (* (- 1) J)) 1)
     (>= (+ K J) 7)
     (>= (+ I (* (- 1) L)) 0)
     (>= (+ I (* (- 1) K)) 1)
     (>= (+ I (* (- 1) G)) 2)
     (>= (+ I (* (- 1) F)) 0)
     (>= (+ I (* (- 1) B)) 3)
     (>= (+ I (* (- 1) J)) 2)
     (>= (+ I L) 9)
     (>= (+ I K) 9)
     (>= (+ I G) 8)
     (>= (+ I F) 10)
     (>= (+ I B) 7)
     (>= (+ I J) 8)
     (>= (+ H L) 5)
     (>= (+ H K) 5)
     (>= (+ H I) 6)
     (>= (+ H G) 4)
     (>= (+ H F) 6)
     (>= (+ H B) 3)
     (>= (+ H J) 4)
     (>= (+ G L) 7)
     (>= (+ G K) 7)
     (>= (+ G J) 6)
     (>= (+ F (* (- 1) L)) 0)
     (>= (+ F (* (- 1) K)) 1)
     (>= (+ F (* (- 1) G)) 2)
     (>= (+ F (* (- 1) J)) 2)
     (>= (+ F L) 9)
     (>= (+ F K) 9)
     (>= (+ F G) 8)
     (>= (+ F J) 8)
     (>= (+ E (* (- 1) N)) (- 1))
     (>= (+ E (* (- 1) H)) 1)
     (>= (+ E (* (- 1) G)) (- 1))
     (>= (+ E (* (- 1) C)) 1)
     (>= (+ E (* (- 1) B)) 0)
     (>= (+ E (* (- 1) A)) (- 1))
     (>= (+ E N) 5)
     (>= (+ E L) 6)
     (>= (+ E K) 6)
     (>= (+ E I) 7)
     (>= (+ E H) 3)
     (>= (+ E G) 5)
     (>= (+ E F) 7)
     (>= (+ E C) 3)
     (>= (+ E B) 4)
     (>= (+ E A) 5)
     (>= (+ E J) 5)
     (>= (+ D (* (- 1) N)) 3)
     (>= (+ D (* (- 1) L)) 1)
     (>= (+ D (* (- 1) K)) 2)
     (>= (+ D (* (- 1) I)) 1)
     (>= (+ D (* (- 1) H)) 5)
     (>= (+ D (* (- 1) G)) 3)
     (>= (+ D (* (- 1) F)) 1)
     (>= (+ D (* (- 1) E)) 4)
     (>= (+ D (* (- 1) C)) 5)
     (>= (+ D (* (- 1) B)) 4)
     (>= (+ D (* (- 1) A)) 3)
     (>= (+ D (* (- 1) J)) 3)
     (>= (+ D N) 9)
     (>= (+ D L) 10)
     (>= (+ D K) 10)
     (>= (+ D I) 11)
     (>= (+ D H) 7)
     (>= (+ D G) 9)
     (>= (+ D F) 11)
     (>= (+ D E) 8)
     (>= (+ D C) 7)
     (>= (+ D B) 8)
     (>= (+ D A) 9)
     (>= (+ D J) 9)
     (>= (+ C (* (- 1) H)) 0)
     (>= (+ C N) 4)
     (>= (+ C L) 5)
     (>= (+ C K) 5)
     (>= (+ C I) 6)
     (>= (+ C H) 2)
     (>= (+ C G) 4)
     (>= (+ C F) 6)
     (>= (+ C B) 3)
     (>= (+ C A) 4)
     (>= (+ C J) 4)
     (>= (+ B (* (- 1) G)) (- 1))
     (>= (+ B L) 6)
     (>= (+ B K) 6)
     (>= (+ B G) 5)
     (>= (+ B F) 7)
     (>= (+ B J) 5)
     (>= (+ A (* (- 1) H)) 2)
     (>= (+ A (* (- 1) G)) 0)
     (>= (+ A (* (- 1) B)) 1)
     (>= (+ A L) 7)
     (>= (+ A K) 7)
     (>= (+ A I) 8)
     (>= (+ A H) 4)
     (>= (+ A G) 6)
     (>= (+ A F) 8)
     (>= (+ A B) 5)
     (>= (+ A J) 6)
     (>= N 3)
     (>= L 4)
     (>= K 4)
     (>= I 5)
     (>= H 1)
     (>= G 3)
     (>= F 5)
     (>= E 2)
     (>= D 6)
     (>= C 1)
     (>= B 2)
     (>= A 3)
     (>= J 3)
     (<= H 1)
     (<= C 1)
     (>= (+ (* (- 1) N) L) 1))
      )
      (lturn N A B C D E F G H I J K L M)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) ) 
    (=>
      (and
        (and (>= (+ (* (- 1) N) G) (- 1))
     (>= (+ (* (- 1) N) F) 1)
     (>= (+ (* (- 1) N) B) (- 2))
     (>= (+ (* (- 1) N) A) (- 1))
     (>= (+ (* (- 1) L) J) 1)
     (>= (+ (* (- 1) K) J) 0)
     (>= (+ (* (- 1) I) F) 0)
     (>= (+ (* (- 1) H) L) 0)
     (>= (+ (* (- 1) H) K) 1)
     (>= (+ (* (- 1) H) I) 4)
     (>= (+ (* (- 1) H) G) 2)
     (>= (+ (* (- 1) H) F) 4)
     (>= (+ (* (- 1) H) B) 1)
     (>= (+ (* (- 1) H) J) 2)
     (>= (+ (* (- 1) E) N) 1)
     (>= (+ (* (- 1) E) I) 3)
     (>= (+ (* (- 1) E) G) 1)
     (>= (+ (* (- 1) E) F) 3)
     (>= (+ (* (- 1) E) B) 0)
     (>= (+ (* (- 1) E) A) 1)
     (>= (+ (* (- 1) D) I) (- 1))
     (>= (+ (* (- 1) D) F) (- 1))
     (>= (+ (* (- 1) C) (* (- 1) H)) (- 2))
     (>= (+ (* (- 1) C) N) 2)
     (>= (+ (* (- 1) C) L) 0)
     (>= (+ (* (- 1) C) K) 1)
     (>= (+ (* (- 1) C) I) 4)
     (>= (+ (* (- 1) C) H) 0)
     (>= (+ (* (- 1) C) G) 2)
     (>= (+ (* (- 1) C) F) 4)
     (>= (+ (* (- 1) C) B) 1)
     (>= (+ (* (- 1) C) A) 2)
     (>= (+ (* (- 1) C) J) 2)
     (>= (+ (* (- 1) B) G) 1)
     (>= (+ (* (- 1) B) F) 3)
     (>= (+ (* (- 1) A) I) 2)
     (>= (+ (* (- 1) A) G) 0)
     (>= (+ (* (- 1) A) F) 2)
     (>= (+ (* (- 1) A) B) (- 1))
     (>= (+ N (* (- 1) H)) 2)
     (>= (+ N (* (- 1) G)) 0)
     (>= (+ N (* (- 1) B)) 1)
     (>= (+ N (* (- 1) A)) 0)
     (>= (+ N L) 4)
     (>= (+ N K) 5)
     (>= (+ N I) 8)
     (>= (+ N H) 4)
     (>= (+ N G) 6)
     (>= (+ N F) 8)
     (>= (+ N B) 5)
     (>= (+ N A) 6)
     (>= (+ N J) 6)
     (>= (+ L K) 3)
     (>= (+ L J) 4)
     (>= (+ K J) 5)
     (>= (+ I (* (- 1) L)) 1)
     (>= (+ I (* (- 1) K)) 0)
     (>= (+ I (* (- 1) G)) 2)
     (>= (+ I (* (- 1) F)) 0)
     (>= (+ I (* (- 1) B)) 3)
     (>= (+ I (* (- 1) J)) 0)
     (>= (+ I L) 6)
     (>= (+ I K) 7)
     (>= (+ I G) 8)
     (>= (+ I F) 10)
     (>= (+ I B) 7)
     (>= (+ I J) 8)
     (>= (+ H L) 2)
     (>= (+ H K) 3)
     (>= (+ H I) 6)
     (>= (+ H G) 4)
     (>= (+ H F) 6)
     (>= (+ H B) 3)
     (>= (+ H J) 4)
     (>= (+ G L) 4)
     (>= (+ G K) 5)
     (>= (+ G J) 6)
     (>= (+ F (* (- 1) L)) 1)
     (>= (+ F (* (- 1) K)) 0)
     (>= (+ F (* (- 1) G)) 2)
     (>= (+ F (* (- 1) J)) 0)
     (>= (+ F L) 6)
     (>= (+ F K) 7)
     (>= (+ F G) 8)
     (>= (+ F J) 8)
     (>= (+ E (* (- 1) N)) (- 2))
     (>= (+ E (* (- 1) H)) 1)
     (>= (+ E (* (- 1) G)) (- 1))
     (>= (+ E (* (- 1) C)) 1)
     (>= (+ E (* (- 1) B)) 0)
     (>= (+ E (* (- 1) A)) (- 1))
     (>= (+ E N) 5)
     (>= (+ E L) 3)
     (>= (+ E K) 4)
     (>= (+ E I) 7)
     (>= (+ E H) 3)
     (>= (+ E G) 5)
     (>= (+ E F) 7)
     (>= (+ E C) 3)
     (>= (+ E B) 4)
     (>= (+ E A) 5)
     (>= (+ E J) 5)
     (>= (+ D (* (- 1) N)) 2)
     (>= (+ D (* (- 1) L)) 2)
     (>= (+ D (* (- 1) K)) 1)
     (>= (+ D (* (- 1) I)) 1)
     (>= (+ D (* (- 1) H)) 5)
     (>= (+ D (* (- 1) G)) 3)
     (>= (+ D (* (- 1) F)) 1)
     (>= (+ D (* (- 1) E)) 4)
     (>= (+ D (* (- 1) C)) 5)
     (>= (+ D (* (- 1) B)) 4)
     (>= (+ D (* (- 1) A)) 3)
     (>= (+ D (* (- 1) J)) 1)
     (>= (+ D N) 9)
     (>= (+ D L) 7)
     (>= (+ D K) 8)
     (>= (+ D I) 11)
     (>= (+ D H) 7)
     (>= (+ D G) 9)
     (>= (+ D F) 11)
     (>= (+ D E) 8)
     (>= (+ D C) 7)
     (>= (+ D B) 8)
     (>= (+ D A) 9)
     (>= (+ D J) 9)
     (>= (+ C (* (- 1) H)) 0)
     (>= (+ C N) 4)
     (>= (+ C L) 2)
     (>= (+ C K) 3)
     (>= (+ C I) 6)
     (>= (+ C H) 2)
     (>= (+ C G) 4)
     (>= (+ C F) 6)
     (>= (+ C B) 3)
     (>= (+ C A) 4)
     (>= (+ C J) 4)
     (>= (+ B (* (- 1) G)) (- 1))
     (>= (+ B L) 3)
     (>= (+ B K) 4)
     (>= (+ B G) 5)
     (>= (+ B F) 7)
     (>= (+ B J) 5)
     (>= (+ A (* (- 1) H)) 2)
     (>= (+ A (* (- 1) G)) 0)
     (>= (+ A (* (- 1) B)) 1)
     (>= (+ A L) 4)
     (>= (+ A K) 5)
     (>= (+ A I) 8)
     (>= (+ A H) 4)
     (>= (+ A G) 6)
     (>= (+ A F) 8)
     (>= (+ A B) 5)
     (>= (+ A J) 6)
     (>= N 3)
     (>= L 1)
     (>= K 2)
     (>= I 5)
     (>= H 1)
     (>= G 3)
     (>= F 5)
     (>= E 2)
     (>= D 6)
     (>= C 1)
     (>= B 2)
     (>= A 3)
     (>= J 3)
     (<= H 1)
     (<= C 1)
     (>= (+ (* (- 1) N) I) 1))
      )
      (lturn N A B C D E F G H I J K L M)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) ) 
    (=>
      (and
        (and (>= (+ (* (- 1) N) G) (- 1))
     (>= (+ (* (- 1) N) F) 0)
     (>= (+ (* (- 1) N) B) (- 2))
     (>= (+ (* (- 1) N) A) (- 1))
     (>= (+ (* (- 1) L) J) 1)
     (>= (+ (* (- 1) K) J) 0)
     (>= (+ (* (- 1) I) G) (- 1))
     (>= (+ (* (- 1) I) F) 0)
     (>= (+ (* (- 1) I) B) (- 2))
     (>= (+ (* (- 1) H) L) 0)
     (>= (+ (* (- 1) H) K) 1)
     (>= (+ (* (- 1) H) I) 3)
     (>= (+ (* (- 1) H) G) 2)
     (>= (+ (* (- 1) H) F) 3)
     (>= (+ (* (- 1) H) B) 1)
     (>= (+ (* (- 1) H) J) 2)
     (>= (+ (* (- 1) F) G) (- 1))
     (>= (+ (* (- 1) E) N) 2)
     (>= (+ (* (- 1) E) I) 2)
     (>= (+ (* (- 1) E) G) 1)
     (>= (+ (* (- 1) E) F) 2)
     (>= (+ (* (- 1) E) B) 0)
     (>= (+ (* (- 1) E) A) 1)
     (>= (+ (* (- 1) D) N) (- 1))
     (>= (+ (* (- 1) D) I) (- 1))
     (>= (+ (* (- 1) D) G) (- 2))
     (>= (+ (* (- 1) D) F) (- 1))
     (>= (+ (* (- 1) D) E) (- 3))
     (>= (+ (* (- 1) D) B) (- 3))
     (>= (+ (* (- 1) D) A) (- 2))
     (>= (+ (* (- 1) C) (* (- 1) H)) (- 2))
     (>= (+ (* (- 1) C) N) 3)
     (>= (+ (* (- 1) C) L) 0)
     (>= (+ (* (- 1) C) K) 1)
     (>= (+ (* (- 1) C) I) 3)
     (>= (+ (* (- 1) C) H) 0)
     (>= (+ (* (- 1) C) G) 2)
     (>= (+ (* (- 1) C) F) 3)
     (>= (+ (* (- 1) C) B) 1)
     (>= (+ (* (- 1) C) A) 2)
     (>= (+ (* (- 1) C) J) 2)
     (>= (+ (* (- 1) B) G) 1)
     (>= (+ (* (- 1) B) F) 2)
     (>= (+ (* (- 1) A) I) 1)
     (>= (+ (* (- 1) A) G) 0)
     (>= (+ (* (- 1) A) F) 1)
     (>= (+ (* (- 1) A) B) (- 1))
     (>= (+ N (* (- 1) L)) 1)
     (>= (+ N (* (- 1) K)) 0)
     (>= (+ N (* (- 1) I)) 0)
     (>= (+ N (* (- 1) H)) 3)
     (>= (+ N (* (- 1) G)) 1)
     (>= (+ N (* (- 1) F)) 0)
     (>= (+ N (* (- 1) B)) 2)
     (>= (+ N (* (- 1) A)) 1)
     (>= (+ N (* (- 1) J)) 0)
     (>= (+ N L) 5)
     (>= (+ N K) 6)
     (>= (+ N I) 8)
     (>= (+ N H) 5)
     (>= (+ N G) 7)
     (>= (+ N F) 8)
     (>= (+ N B) 6)
     (>= (+ N A) 7)
     (>= (+ N J) 7)
     (>= (+ L K) 3)
     (>= (+ L J) 4)
     (>= (+ K J) 5)
     (>= (+ I (* (- 1) L)) 1)
     (>= (+ I (* (- 1) K)) 0)
     (>= (+ I (* (- 1) G)) 1)
     (>= (+ I (* (- 1) F)) 0)
     (>= (+ I (* (- 1) B)) 2)
     (>= (+ I (* (- 1) J)) 0)
     (>= (+ I L) 5)
     (>= (+ I K) 6)
     (>= (+ I G) 7)
     (>= (+ I F) 8)
     (>= (+ I B) 6)
     (>= (+ I J) 7)
     (>= (+ H L) 2)
     (>= (+ H K) 3)
     (>= (+ H I) 5)
     (>= (+ H G) 4)
     (>= (+ H F) 5)
     (>= (+ H B) 3)
     (>= (+ H J) 4)
     (>= (+ G (* (- 1) L)) 0)
     (>= (+ G (* (- 1) K)) (- 1))
     (>= (+ G (* (- 1) J)) (- 1))
     (>= (+ G L) 4)
     (>= (+ G K) 5)
     (>= (+ G J) 6)
     (>= (+ F (* (- 1) L)) 1)
     (>= (+ F (* (- 1) K)) 0)
     (>= (+ F (* (- 1) G)) 1)
     (>= (+ F (* (- 1) J)) 0)
     (>= (+ F L) 5)
     (>= (+ F K) 6)
     (>= (+ F G) 7)
     (>= (+ F J) 7)
     (>= (+ E (* (- 1) N)) (- 2))
     (>= (+ E (* (- 1) L)) (- 1))
     (>= (+ E (* (- 1) K)) (- 2))
     (>= (+ E (* (- 1) I)) (- 2))
     (>= (+ E (* (- 1) H)) 1)
     (>= (+ E (* (- 1) G)) (- 1))
     (>= (+ E (* (- 1) F)) (- 2))
     (>= (+ E (* (- 1) C)) 1)
     (>= (+ E (* (- 1) B)) 0)
     (>= (+ E (* (- 1) A)) (- 1))
     (>= (+ E (* (- 1) J)) (- 2))
     (>= (+ E N) 6)
     (>= (+ E L) 3)
     (>= (+ E K) 4)
     (>= (+ E I) 6)
     (>= (+ E H) 3)
     (>= (+ E G) 5)
     (>= (+ E F) 6)
     (>= (+ E C) 3)
     (>= (+ E B) 4)
     (>= (+ E A) 5)
     (>= (+ E J) 5)
     (>= (+ D (* (- 1) N)) 1)
     (>= (+ D (* (- 1) L)) 2)
     (>= (+ D (* (- 1) K)) 1)
     (>= (+ D (* (- 1) I)) 1)
     (>= (+ D (* (- 1) H)) 4)
     (>= (+ D (* (- 1) G)) 2)
     (>= (+ D (* (- 1) F)) 1)
     (>= (+ D (* (- 1) E)) 3)
     (>= (+ D (* (- 1) C)) 4)
     (>= (+ D (* (- 1) B)) 3)
     (>= (+ D (* (- 1) A)) 2)
     (>= (+ D (* (- 1) J)) 1)
     (>= (+ D N) 9)
     (>= (+ D L) 6)
     (>= (+ D K) 7)
     (>= (+ D I) 9)
     (>= (+ D H) 6)
     (>= (+ D G) 8)
     (>= (+ D F) 9)
     (>= (+ D E) 7)
     (>= (+ D C) 6)
     (>= (+ D B) 7)
     (>= (+ D A) 8)
     (>= (+ D J) 8)
     (>= (+ C (* (- 1) H)) 0)
     (>= (+ C N) 5)
     (>= (+ C L) 2)
     (>= (+ C K) 3)
     (>= (+ C I) 5)
     (>= (+ C H) 2)
     (>= (+ C G) 4)
     (>= (+ C F) 5)
     (>= (+ C B) 3)
     (>= (+ C A) 4)
     (>= (+ C J) 4)
     (>= (+ B (* (- 1) L)) (- 1))
     (>= (+ B (* (- 1) K)) (- 2))
     (>= (+ B (* (- 1) G)) (- 1))
     (>= (+ B (* (- 1) F)) (- 2))
     (>= (+ B (* (- 1) J)) (- 2))
     (>= (+ B L) 3)
     (>= (+ B K) 4)
     (>= (+ B G) 5)
     (>= (+ B F) 6)
     (>= (+ B J) 5)
     (>= (+ A (* (- 1) L)) 0)
     (>= (+ A (* (- 1) K)) (- 1))
     (>= (+ A (* (- 1) I)) (- 1))
     (>= (+ A (* (- 1) H)) 2)
     (>= (+ A (* (- 1) G)) 0)
     (>= (+ A (* (- 1) F)) (- 1))
     (>= (+ A (* (- 1) B)) 1)
     (>= (+ A (* (- 1) J)) (- 1))
     (>= (+ A L) 4)
     (>= (+ A K) 5)
     (>= (+ A I) 7)
     (>= (+ A H) 4)
     (>= (+ A G) 6)
     (>= (+ A F) 7)
     (>= (+ A B) 5)
     (>= (+ A J) 6)
     (>= N 4)
     (>= L 1)
     (>= K 2)
     (>= I 4)
     (>= H 1)
     (>= G 3)
     (>= F 4)
     (>= E 2)
     (>= D 5)
     (>= C 1)
     (>= B 2)
     (>= A 3)
     (>= J 3)
     (<= H 1)
     (<= C 1)
     (>= (+ (* (- 1) N) I) 0))
      )
      (lturn N A B C D E F G H I J K L M)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) ) 
    (=>
      (and
        (and (>= (+ (* (- 1) N) K) (- 1))
     (>= (+ (* (- 1) N) I) 0)
     (>= (+ (* (- 1) N) G) (- 1))
     (>= (+ (* (- 1) N) F) 0)
     (>= (+ (* (- 1) N) B) (- 2))
     (>= (+ (* (- 1) N) A) (- 1))
     (>= (+ (* (- 1) N) J) (- 2))
     (>= (+ (* (- 1) L) K) (- 1))
     (>= (+ (* (- 1) L) J) (- 2))
     (>= (+ (* (- 1) K) J) (- 1))
     (>= (+ (* (- 1) I) F) 0)
     (>= (+ (* (- 1) H) L) 2)
     (>= (+ (* (- 1) H) K) 2)
     (>= (+ (* (- 1) H) I) 3)
     (>= (+ (* (- 1) H) G) 2)
     (>= (+ (* (- 1) H) F) 3)
     (>= (+ (* (- 1) H) B) 1)
     (>= (+ (* (- 1) H) J) 1)
     (>= (+ (* (- 1) G) L) 0)
     (>= (+ (* (- 1) G) K) 0)
     (>= (+ (* (- 1) G) J) (- 1))
     (>= (+ (* (- 1) E) N) 1)
     (>= (+ (* (- 1) E) L) 1)
     (>= (+ (* (- 1) E) K) 1)
     (>= (+ (* (- 1) E) I) 2)
     (>= (+ (* (- 1) E) G) 1)
     (>= (+ (* (- 1) E) F) 2)
     (>= (+ (* (- 1) E) B) 0)
     (>= (+ (* (- 1) E) A) 1)
     (>= (+ (* (- 1) E) J) 0)
     (>= (+ (* (- 1) D) I) (- 1))
     (>= (+ (* (- 1) D) F) (- 1))
     (>= (+ (* (- 1) C) (* (- 1) H)) (- 2))
     (>= (+ (* (- 1) C) N) 2)
     (>= (+ (* (- 1) C) L) 2)
     (>= (+ (* (- 1) C) K) 2)
     (>= (+ (* (- 1) C) I) 3)
     (>= (+ (* (- 1) C) H) 0)
     (>= (+ (* (- 1) C) G) 2)
     (>= (+ (* (- 1) C) F) 3)
     (>= (+ (* (- 1) C) B) 1)
     (>= (+ (* (- 1) C) A) 2)
     (>= (+ (* (- 1) C) J) 1)
     (>= (+ (* (- 1) B) L) 1)
     (>= (+ (* (- 1) B) K) 1)
     (>= (+ (* (- 1) B) G) 1)
     (>= (+ (* (- 1) B) F) 2)
     (>= (+ (* (- 1) B) J) 0)
     (>= (+ (* (- 1) A) L) 0)
     (>= (+ (* (- 1) A) K) 0)
     (>= (+ (* (- 1) A) I) 1)
     (>= (+ (* (- 1) A) G) 0)
     (>= (+ (* (- 1) A) F) 1)
     (>= (+ (* (- 1) A) B) (- 1))
     (>= (+ (* (- 1) A) J) (- 1))
     (>= (+ N (* (- 1) L)) 0)
     (>= (+ N (* (- 1) K)) 0)
     (>= (+ N (* (- 1) H)) 2)
     (>= (+ N (* (- 1) G)) 0)
     (>= (+ N (* (- 1) B)) 1)
     (>= (+ N (* (- 1) A)) 0)
     (>= (+ N (* (- 1) J)) 1)
     (>= (+ N L) 6)
     (>= (+ N K) 6)
     (>= (+ N I) 7)
     (>= (+ N H) 4)
     (>= (+ N G) 6)
     (>= (+ N F) 7)
     (>= (+ N B) 5)
     (>= (+ N A) 6)
     (>= (+ N J) 5)
     (>= (+ L (* (- 1) K)) 0)
     (>= (+ L (* (- 1) J)) 1)
     (>= (+ L K) 6)
     (>= (+ L J) 5)
     (>= (+ K (* (- 1) J)) 1)
     (>= (+ K J) 5)
     (>= (+ I (* (- 1) L)) 0)
     (>= (+ I (* (- 1) K)) 1)
     (>= (+ I (* (- 1) G)) 1)
     (>= (+ I (* (- 1) F)) 0)
     (>= (+ I (* (- 1) B)) 2)
     (>= (+ I (* (- 1) J)) 2)
     (>= (+ I L) 7)
     (>= (+ I K) 7)
     (>= (+ I G) 7)
     (>= (+ I F) 8)
     (>= (+ I B) 6)
     (>= (+ I J) 6)
     (>= (+ H L) 4)
     (>= (+ H K) 4)
     (>= (+ H I) 5)
     (>= (+ H G) 4)
     (>= (+ H F) 5)
     (>= (+ H B) 3)
     (>= (+ H J) 3)
     (>= (+ G (* (- 1) L)) (- 1))
     (>= (+ G (* (- 1) K)) 0)
     (>= (+ G (* (- 1) J)) 1)
     (>= (+ G L) 6)
     (>= (+ G K) 6)
     (>= (+ G J) 5)
     (>= (+ F (* (- 1) L)) 0)
     (>= (+ F (* (- 1) K)) 1)
     (>= (+ F (* (- 1) G)) 1)
     (>= (+ F (* (- 1) J)) 2)
     (>= (+ F L) 7)
     (>= (+ F K) 7)
     (>= (+ F G) 7)
     (>= (+ F J) 6)
     (>= (+ E (* (- 1) N)) (- 2))
     (>= (+ E (* (- 1) L)) (- 2))
     (>= (+ E (* (- 1) K)) (- 1))
     (>= (+ E (* (- 1) H)) 1)
     (>= (+ E (* (- 1) G)) (- 1))
     (>= (+ E (* (- 1) C)) 1)
     (>= (+ E (* (- 1) B)) 0)
     (>= (+ E (* (- 1) A)) (- 1))
     (>= (+ E (* (- 1) J)) 0)
     (>= (+ E N) 5)
     (>= (+ E L) 5)
     (>= (+ E K) 5)
     (>= (+ E I) 6)
     (>= (+ E H) 3)
     (>= (+ E G) 5)
     (>= (+ E F) 6)
     (>= (+ E C) 3)
     (>= (+ E B) 4)
     (>= (+ E A) 5)
     (>= (+ E J) 4)
     (>= (+ D (* (- 1) N)) 1)
     (>= (+ D (* (- 1) L)) 1)
     (>= (+ D (* (- 1) K)) 2)
     (>= (+ D (* (- 1) I)) 1)
     (>= (+ D (* (- 1) H)) 4)
     (>= (+ D (* (- 1) G)) 2)
     (>= (+ D (* (- 1) F)) 1)
     (>= (+ D (* (- 1) E)) 3)
     (>= (+ D (* (- 1) C)) 4)
     (>= (+ D (* (- 1) B)) 3)
     (>= (+ D (* (- 1) A)) 2)
     (>= (+ D (* (- 1) J)) 3)
     (>= (+ D N) 8)
     (>= (+ D L) 8)
     (>= (+ D K) 8)
     (>= (+ D I) 9)
     (>= (+ D H) 6)
     (>= (+ D G) 8)
     (>= (+ D F) 9)
     (>= (+ D E) 7)
     (>= (+ D C) 6)
     (>= (+ D B) 7)
     (>= (+ D A) 8)
     (>= (+ D J) 7)
     (>= (+ C (* (- 1) H)) 0)
     (>= (+ C N) 4)
     (>= (+ C L) 4)
     (>= (+ C K) 4)
     (>= (+ C I) 5)
     (>= (+ C H) 2)
     (>= (+ C G) 4)
     (>= (+ C F) 5)
     (>= (+ C B) 3)
     (>= (+ C A) 4)
     (>= (+ C J) 3)
     (>= (+ B (* (- 1) L)) (- 2))
     (>= (+ B (* (- 1) K)) (- 1))
     (>= (+ B (* (- 1) G)) (- 1))
     (>= (+ B (* (- 1) J)) 0)
     (>= (+ B L) 5)
     (>= (+ B K) 5)
     (>= (+ B G) 5)
     (>= (+ B F) 6)
     (>= (+ B J) 4)
     (>= (+ A (* (- 1) L)) (- 1))
     (>= (+ A (* (- 1) K)) 0)
     (>= (+ A (* (- 1) H)) 2)
     (>= (+ A (* (- 1) G)) 0)
     (>= (+ A (* (- 1) B)) 1)
     (>= (+ A (* (- 1) J)) 1)
     (>= (+ A L) 6)
     (>= (+ A K) 6)
     (>= (+ A I) 7)
     (>= (+ A H) 4)
     (>= (+ A G) 6)
     (>= (+ A F) 7)
     (>= (+ A B) 5)
     (>= (+ A J) 5)
     (>= N 3)
     (>= L 3)
     (>= K 3)
     (>= I 4)
     (>= H 1)
     (>= G 3)
     (>= F 4)
     (>= E 2)
     (>= D 5)
     (>= C 1)
     (>= B 2)
     (>= A 3)
     (>= J 2)
     (<= H 1)
     (<= C 1)
     (>= (+ (* (- 1) N) L) 0))
      )
      (step_lturn__bar N A B C D E F G H I J K L M)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) ) 
    (=>
      (and
        (lturn N A B C D E F G H I J K L M)
        true
      )
      (combined_lturn N A B C D E F G H I J K L M)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) ) 
    (=>
      (and
        (step_lturn N A B C D E F G H I J K L M)
        true
      )
      (combined_lturn N A B C D E F G H I J K L M)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) ) 
    (=>
      (and
        (step_lturn__bar N A B C D E F G H I J K L M)
        true
      )
      (combined_lturn__bar N A B C D E F G H I J K L M)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) ) 
    (=>
      (and
        (step_lturn K A B C D E F G H I M L N J)
        true
      )
      (lturn K A B C D E F G H I N M L J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) ) 
    (=>
      (and
        (step_lturn__bar K A B C D E F G H I N L M J)
        true
      )
      (lturn K A B C D E F G H I N M L J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (v_14 Int) (v_15 Int) (v_16 Int) ) 
    (=>
      (and
        (combined_lturn K A B C D E F G H I v_14 L N J)
        (step_lturn K A B C D E F G H I v_15 M L J)
        (combined_lturn K A B C D E F G H I v_16 N M J)
        (and (= v_14 K) (= v_15 K) (= v_16 K))
      )
      (lturn K A B C D E F G H I N M L J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (v_14 Int) (v_15 Int) (v_16 Int) ) 
    (=>
      (and
        (combined_lturn K A B C D E F G H I v_14 L N J)
        (combined_lturn K A B C D E F G H I v_15 M L J)
        (step_lturn K A B C D E F G H I v_16 N M J)
        (and (= v_14 K) (= v_15 K) (= v_16 K))
      )
      (lturn K A B C D E F G H I N M L J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (v_14 Int) (v_15 Int) (v_16 Int) ) 
    (=>
      (and
        (step_lturn K A B C D E F G H I v_14 L N J)
        (combined_lturn K A B C D E F G H I v_15 M L J)
        (combined_lturn K A B C D E F G H I v_16 N M J)
        (and (= v_14 K) (= v_15 K) (= v_16 K))
      )
      (lturn K A B C D E F G H I N M L J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (v_15 Int) (v_16 Int) (v_17 Int) ) 
    (=>
      (and
        (combined_lturn L A B C D E F G H I K N v_15 J)
        (step_lturn L A B C D E F G H I O N M J)
        (combined_lturn L A B C D E F G H I v_16 N M J)
        (combined_lturn L A B C D E F G H I v_17 O N J)
        (combined_lturn L A B C D E F G H I K O N J)
        (and (= v_15 L) (= v_16 L) (= v_17 L))
      )
      (lturn L A B C D E F G H I K N M J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (v_15 Int) (v_16 Int) (v_17 Int) ) 
    (=>
      (and
        (combined_lturn L A B C D E F G H I K N v_15 J)
        (combined_lturn L A B C D E F G H I O N M J)
        (step_lturn L A B C D E F G H I v_16 N M J)
        (combined_lturn L A B C D E F G H I v_17 O N J)
        (combined_lturn L A B C D E F G H I K O N J)
        (and (= v_15 L) (= v_16 L) (= v_17 L))
      )
      (lturn L A B C D E F G H I K N M J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (v_15 Int) (v_16 Int) (v_17 Int) ) 
    (=>
      (and
        (combined_lturn L A B C D E F G H I K N v_15 J)
        (combined_lturn L A B C D E F G H I O N M J)
        (combined_lturn L A B C D E F G H I v_16 N M J)
        (step_lturn L A B C D E F G H I v_17 O N J)
        (combined_lturn L A B C D E F G H I K O N J)
        (and (= v_15 L) (= v_16 L) (= v_17 L))
      )
      (lturn L A B C D E F G H I K N M J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (v_15 Int) (v_16 Int) (v_17 Int) ) 
    (=>
      (and
        (combined_lturn L A B C D E F G H I K N v_15 J)
        (combined_lturn L A B C D E F G H I O N M J)
        (combined_lturn L A B C D E F G H I v_16 N M J)
        (combined_lturn L A B C D E F G H I v_17 O N J)
        (step_lturn L A B C D E F G H I K O N J)
        (and (= v_15 L) (= v_16 L) (= v_17 L))
      )
      (lturn L A B C D E F G H I K N M J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (v_15 Int) (v_16 Int) (v_17 Int) ) 
    (=>
      (and
        (step_lturn L A B C D E F G H I K N v_15 J)
        (combined_lturn L A B C D E F G H I O N M J)
        (combined_lturn L A B C D E F G H I v_16 N M J)
        (combined_lturn L A B C D E F G H I v_17 O N J)
        (combined_lturn L A B C D E F G H I K O N J)
        (and (= v_15 L) (= v_16 L) (= v_17 L))
      )
      (lturn L A B C D E F G H I K N M J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) ) 
    (=>
      (and
        (step_lturn K A B C D E F G H I M L N J)
        true
      )
      (step_lturn K A B C D E F G H I N M L J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) ) 
    (=>
      (and
        (step_lturn__bar K A B C D E F G H I N L M J)
        true
      )
      (step_lturn K A B C D E F G H I N M L J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (v_14 Int) (v_15 Int) (v_16 Int) ) 
    (=>
      (and
        (combined_lturn K A B C D E F G H I v_14 L N J)
        (step_lturn K A B C D E F G H I v_15 M L J)
        (combined_lturn K A B C D E F G H I v_16 N M J)
        (and (= v_14 K) (= v_15 K) (= v_16 K))
      )
      (step_lturn K A B C D E F G H I N M L J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (v_14 Int) (v_15 Int) (v_16 Int) ) 
    (=>
      (and
        (combined_lturn K A B C D E F G H I v_14 L N J)
        (combined_lturn K A B C D E F G H I v_15 M L J)
        (step_lturn K A B C D E F G H I v_16 N M J)
        (and (= v_14 K) (= v_15 K) (= v_16 K))
      )
      (step_lturn K A B C D E F G H I N M L J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (v_14 Int) (v_15 Int) (v_16 Int) ) 
    (=>
      (and
        (step_lturn K A B C D E F G H I v_14 L N J)
        (combined_lturn K A B C D E F G H I v_15 M L J)
        (combined_lturn K A B C D E F G H I v_16 N M J)
        (and (= v_14 K) (= v_15 K) (= v_16 K))
      )
      (step_lturn K A B C D E F G H I N M L J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (v_15 Int) (v_16 Int) (v_17 Int) ) 
    (=>
      (and
        (combined_lturn L A B C D E F G H I K N v_15 J)
        (step_lturn L A B C D E F G H I O N M J)
        (combined_lturn L A B C D E F G H I v_16 N M J)
        (combined_lturn L A B C D E F G H I v_17 O N J)
        (combined_lturn L A B C D E F G H I K O N J)
        (and (= v_15 L) (= v_16 L) (= v_17 L))
      )
      (step_lturn L A B C D E F G H I K N M J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (v_15 Int) (v_16 Int) (v_17 Int) ) 
    (=>
      (and
        (combined_lturn L A B C D E F G H I K N v_15 J)
        (combined_lturn L A B C D E F G H I O N M J)
        (step_lturn L A B C D E F G H I v_16 N M J)
        (combined_lturn L A B C D E F G H I v_17 O N J)
        (combined_lturn L A B C D E F G H I K O N J)
        (and (= v_15 L) (= v_16 L) (= v_17 L))
      )
      (step_lturn L A B C D E F G H I K N M J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (v_15 Int) (v_16 Int) (v_17 Int) ) 
    (=>
      (and
        (combined_lturn L A B C D E F G H I K N v_15 J)
        (combined_lturn L A B C D E F G H I O N M J)
        (combined_lturn L A B C D E F G H I v_16 N M J)
        (step_lturn L A B C D E F G H I v_17 O N J)
        (combined_lturn L A B C D E F G H I K O N J)
        (and (= v_15 L) (= v_16 L) (= v_17 L))
      )
      (step_lturn L A B C D E F G H I K N M J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (v_15 Int) (v_16 Int) (v_17 Int) ) 
    (=>
      (and
        (combined_lturn L A B C D E F G H I K N v_15 J)
        (combined_lturn L A B C D E F G H I O N M J)
        (combined_lturn L A B C D E F G H I v_16 N M J)
        (combined_lturn L A B C D E F G H I v_17 O N J)
        (step_lturn L A B C D E F G H I K O N J)
        (and (= v_15 L) (= v_16 L) (= v_17 L))
      )
      (step_lturn L A B C D E F G H I K N M J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (v_15 Int) (v_16 Int) (v_17 Int) ) 
    (=>
      (and
        (step_lturn L A B C D E F G H I K N v_15 J)
        (combined_lturn L A B C D E F G H I O N M J)
        (combined_lturn L A B C D E F G H I v_16 N M J)
        (combined_lturn L A B C D E F G H I v_17 O N J)
        (combined_lturn L A B C D E F G H I K O N J)
        (and (= v_15 L) (= v_16 L) (= v_17 L))
      )
      (step_lturn L A B C D E F G H I K N M J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (v_15 Int) (v_16 Int) (v_17 Int) ) 
    (=>
      (and
        (combined_lturn L A B C D E F G H I K N v_15 J)
        (step_lturn L A B C D E F G H I K M N J)
        (combined_lturn L A B C D E F G H I O N M J)
        (combined_lturn L A B C D E F G H I v_16 N M J)
        (combined_lturn L A B C D E F G H I v_17 O N J)
        (combined_lturn L A B C D E F G H I K O N J)
        (and (= v_15 L) (= v_16 L) (= v_17 L))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (v_15 Int) (v_16 Int) (v_17 Int) ) 
    (=>
      (and
        (step_lturn L A B C D E F G H I K N v_15 J)
        (combined_lturn L A B C D E F G H I K M N J)
        (combined_lturn L A B C D E F G H I O N M J)
        (combined_lturn L A B C D E F G H I v_16 N M J)
        (combined_lturn L A B C D E F G H I v_17 O N J)
        (combined_lturn L A B C D E F G H I K O N J)
        (and (= v_15 L) (= v_16 L) (= v_17 L))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (v_15 Int) (v_16 Int) (v_17 Int) ) 
    (=>
      (and
        (combined_lturn L A B C D E F G H I K N v_15 J)
        (combined_lturn L A B C D E F G H I K M N J)
        (combined_lturn L A B C D E F G H I O N M J)
        (combined_lturn L A B C D E F G H I v_16 N M J)
        (combined_lturn L A B C D E F G H I v_17 O N J)
        (step_lturn L A B C D E F G H I K O N J)
        (and (= v_15 L) (= v_16 L) (= v_17 L))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (v_15 Int) (v_16 Int) (v_17 Int) ) 
    (=>
      (and
        (combined_lturn L A B C D E F G H I K N v_15 J)
        (combined_lturn L A B C D E F G H I K M N J)
        (combined_lturn L A B C D E F G H I O N M J)
        (combined_lturn L A B C D E F G H I v_16 N M J)
        (step_lturn L A B C D E F G H I v_17 O N J)
        (combined_lturn L A B C D E F G H I K O N J)
        (and (= v_15 L) (= v_16 L) (= v_17 L))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (v_15 Int) (v_16 Int) (v_17 Int) ) 
    (=>
      (and
        (combined_lturn L A B C D E F G H I K N v_15 J)
        (combined_lturn L A B C D E F G H I K M N J)
        (combined_lturn L A B C D E F G H I O N M J)
        (step_lturn L A B C D E F G H I v_16 N M J)
        (combined_lturn L A B C D E F G H I v_17 O N J)
        (combined_lturn L A B C D E F G H I K O N J)
        (and (= v_15 L) (= v_16 L) (= v_17 L))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (v_15 Int) (v_16 Int) (v_17 Int) ) 
    (=>
      (and
        (combined_lturn L A B C D E F G H I K N v_15 J)
        (combined_lturn L A B C D E F G H I K M N J)
        (step_lturn L A B C D E F G H I O N M J)
        (combined_lturn L A B C D E F G H I v_16 N M J)
        (combined_lturn L A B C D E F G H I v_17 O N J)
        (combined_lturn L A B C D E F G H I K O N J)
        (and (= v_15 L) (= v_16 L) (= v_17 L))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (v_14 Int) (v_15 Int) (v_16 Int) ) 
    (=>
      (and
        (combined_lturn K A B C D E F G H I v_14 L N J)
        (step_lturn K A B C D E F G H I N L M J)
        (combined_lturn K A B C D E F G H I v_15 M L J)
        (combined_lturn K A B C D E F G H I v_16 N M J)
        (and (= v_14 K) (= v_15 K) (= v_16 K))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (v_14 Int) (v_15 Int) (v_16 Int) ) 
    (=>
      (and
        (step_lturn K A B C D E F G H I v_14 L N J)
        (combined_lturn K A B C D E F G H I N L M J)
        (combined_lturn K A B C D E F G H I v_15 M L J)
        (combined_lturn K A B C D E F G H I v_16 N M J)
        (and (= v_14 K) (= v_15 K) (= v_16 K))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (v_14 Int) (v_15 Int) (v_16 Int) ) 
    (=>
      (and
        (combined_lturn K A B C D E F G H I v_14 L N J)
        (combined_lturn K A B C D E F G H I N L M J)
        (combined_lturn K A B C D E F G H I v_15 M L J)
        (step_lturn K A B C D E F G H I v_16 N M J)
        (and (= v_14 K) (= v_15 K) (= v_16 K))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (v_14 Int) (v_15 Int) (v_16 Int) ) 
    (=>
      (and
        (combined_lturn K A B C D E F G H I v_14 L N J)
        (combined_lturn K A B C D E F G H I N L M J)
        (step_lturn K A B C D E F G H I v_15 M L J)
        (combined_lturn K A B C D E F G H I v_16 N M J)
        (and (= v_14 K) (= v_15 K) (= v_16 K))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) ) 
    (=>
      (and
        (combined_lturn K A B C D E F G H I N M L J)
        (step_lturn K A B C D E F G H I N L M J)
        true
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) ) 
    (=>
      (and
        (step_lturn K A B C D E F G H I N M L J)
        (combined_lturn K A B C D E F G H I N L M J)
        true
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) ) 
    (=>
      (and
        (combined_lturn__bar K A B C D E F G H I N M L J)
        (step_lturn K A B C D E F G H I N M L J)
        true
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) ) 
    (=>
      (and
        (step_lturn__bar K A B C D E F G H I N M L J)
        (combined_lturn K A B C D E F G H I N M L J)
        true
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        CHC_COMP_FALSE
      )
      false
    )
  )
)

(check-sat)
(exit)

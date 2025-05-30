(set-logic HORN)

(declare-datatypes ((|TSLL| 0)) (((|TSLL|  (|TSLL::next| Int) (|TSLL::data| Int)))))
(declare-datatypes ((|HeapObject| 0) (|AddrRange| 0)) (((|O_Int|  (|getInt| Int)) (|O_UInt|  (|getUInt| Int)) (|O_Addr|  (|getAddr| Int)) (|O_AddrRange|  (|getAddrRange| AddrRange)) (|O_TSLL|  (|getTSLL| TSLL)) (|defObj| ))
                                                   ((|AddrRange|  (|AddrRangeStart| Int) (|AddrRangeSize| Int)))))
(declare-datatypes ((|Heap| 0)) (((|HeapCtor|  (|HeapSize| Int) (|HeapContents| (Array Int HeapObject))))))

(declare-fun |inv_main1046_3| ( Heap Int Int Int Int Int ) Bool)
(declare-fun |inv_main_29| ( Heap Int Int Int Int ) Bool)
(declare-fun |inv_main_49| ( Heap Int Int Int Int ) Bool)
(declare-fun |inv_main_5| ( Heap Int Int Int ) Bool)
(declare-fun |inv_main1039_2| ( Heap Int Int Int Int ) Bool)
(declare-fun |inv_main_15| ( Heap Int Int Int ) Bool)
(declare-fun |inv_main_33| ( Heap Int Int Int Int ) Bool)
(declare-fun |inv_main996_2_1| ( Heap Int ) Bool)
(declare-fun |inv_main_35| ( Heap Int Int Int Int ) Bool)
(declare-fun |inv_main1019_4| ( Heap Int Int Int ) Bool)
(declare-fun |inv_main1001_2| ( Heap Int Int Int ) Bool)
(declare-fun |CHC_COMP_FALSE| ( ) Bool)
(declare-fun |inv_main_19| ( Heap Int Int Int ) Bool)
(declare-fun |inv_main| ( Heap Int ) Bool)
(declare-fun |inv_main_44| ( Heap Int Int Int Int ) Bool)
(declare-fun |inv_main1017_4| ( Heap Int Int Int ) Bool)
(declare-fun |inv_main_23| ( Heap Int Int Int ) Bool)
(declare-fun |inv_main_28| ( Heap Int Int Int Int ) Bool)
(declare-fun |inv_main_6| ( Heap Int Int Int ) Bool)
(declare-fun |inv_main1043_3| ( Heap Int Int Int Int ) Bool)
(declare-fun |inv_main_25| ( Heap Int Int Int ) Bool)
(declare-fun |inv_main_17| ( Heap Int Int Int ) Bool)
(declare-fun |inv_main_34| ( Heap Int Int Int Int ) Bool)
(declare-fun |inv_main_55| ( Heap Int Int Int Int ) Bool)
(declare-fun |inv_main1007_3| ( Heap Int Int Int Int ) Bool)
(declare-fun |inv_main_40| ( Heap Int Int Int Int ) Bool)
(declare-fun |inv_main996_2| ( Heap ) Bool)
(declare-fun |inv_main1045_2| ( Heap Int Int Int Int ) Bool)
(declare-fun |inv_main_36| ( Heap Int Int Int Int ) Bool)
(declare-fun |inv_main1027_9| ( Heap Int Int Int Int ) Bool)
(declare-fun |inv_main_16| ( Heap Int Int Int ) Bool)
(declare-fun |inv_main_45| ( Heap Int Int Int Int ) Bool)
(declare-fun |inv_main_31| ( Heap Int Int Int Int ) Bool)

(assert
  (forall ( (A Heap) ) 
    (=>
      (and
        (= A (HeapCtor 0 ((as const (Array Int HeapObject)) defObj)))
      )
      (inv_main996_2 A)
    )
  )
)
(assert
  (forall ( (A Heap) (B Int) (C Int) (D Int) (E Int) (F Heap) ) 
    (=>
      (and
        (inv_main_28 F E D C B)
        (let ((a!1 (ite (and (not (<= B 0)) (>= (HeapSize F) B))
                (select (HeapContents F) B)
                defObj)))
(let ((a!2 (O_TSLL (TSLL 0 (|TSLL::data| (getTSLL a!1))))))
(let ((a!3 (ite (and (not (<= B 0)) (>= (HeapSize F) B))
                (HeapCtor (HeapSize F) (store (HeapContents F) B a!2))
                F)))
  (and (= A a!3) ((_ is O_TSLL) a!1)))))
      )
      (inv_main_29 A E D C B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Heap) (D Int) (E Int) (F Int) (G Int) (H Int) (I Heap) ) 
    (=>
      (and
        (inv_main_6 I H G F)
        (let ((a!1 (ite (and (not (<= G 0)) (>= (HeapSize I) G))
                (select (HeapContents I) G)
                defObj)))
(let ((a!2 (O_TSLL (TSLL 0 (|TSLL::data| (getTSLL a!1))))))
(let ((a!3 (ite (and (not (<= G 0)) (>= (HeapSize I) G))
                (HeapCtor (HeapSize I) (store (HeapContents I) G a!2))
                I)))
  (and (= D 0) (= B H) (= A G) (= E 0) (= E F) (= C a!3) ((_ is O_TSLL) a!1)))))
      )
      (inv_main1019_4 C B A E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Heap) (F Int) (G Int) (H Int) (I Int) (J Int) (K Heap) ) 
    (=>
      (and
        (inv_main_29 K J I H G)
        (let ((a!1 (ite (and (not (<= I 0)) (>= (HeapSize K) I))
                (select (HeapContents K) I)
                defObj)))
  (and (= B H)
       (= A G)
       (not (= F 0))
       (= F (|TSLL::next| (getTSLL a!1)))
       (= D J)
       (= C I)
       (= E K)
       ((_ is O_TSLL) a!1)))
      )
      (inv_main1045_2 E D C B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Heap) ) 
    (=>
      (and
        (inv_main1045_2 F E D C B)
        (let ((a!1 (ite (and (not (<= D 0)) (>= (HeapSize F) D))
                (select (HeapContents F) D)
                defObj)))
  (and (= A (|TSLL::next| (getTSLL a!1))) ((_ is O_TSLL) a!1)))
      )
      (inv_main1046_3 F E D C B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Heap) (E Int) (F Int) (G Int) (H Int) (I Heap) ) 
    (=>
      (and
        (inv_main_17 I H G F)
        (let ((a!1 (ite (and (not (<= G 0)) (>= (HeapSize I) G))
                (select (HeapContents I) G)
                defObj)))
  (and (= C H)
       (= B G)
       (= A F)
       (= E 0)
       (= E (|TSLL::data| (getTSLL a!1)))
       (= D I)
       ((_ is O_TSLL) a!1)))
      )
      (inv_main_19 D C B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Heap) (F Int) (G Int) (H Int) (I Int) (J Heap) ) 
    (=>
      (and
        (inv_main_6 J I H G)
        (let ((a!1 (ite (and (not (<= H 0)) (>= (HeapSize J) H))
                (select (HeapContents J) H)
                defObj)))
(let ((a!2 (O_TSLL (TSLL 0 (|TSLL::data| (getTSLL a!1))))))
(let ((a!3 (ite (and (not (<= H 0)) (>= (HeapSize J) H))
                (HeapCtor (HeapSize J) (store (HeapContents J) H a!2))
                J)))
  (and (= D I)
       (= A 1)
       (= C H)
       (= B G)
       (not (= F 0))
       (= E a!3)
       ((_ is O_TSLL) a!1)))))
      )
      (inv_main1017_4 E D C A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Heap) (D Int) (E Int) (F Int) (G Int) (H Int) (I Heap) ) 
    (=>
      (and
        (inv_main_6 I H G F)
        (let ((a!1 (ite (and (not (<= G 0)) (>= (HeapSize I) G))
                (select (HeapContents I) G)
                defObj)))
(let ((a!2 (O_TSLL (TSLL 0 (|TSLL::data| (getTSLL a!1))))))
(let ((a!3 (ite (and (not (<= G 0)) (>= (HeapSize I) G))
                (HeapCtor (HeapSize I) (store (HeapContents I) G a!2))
                I)))
  (and (= D 0)
       (= B H)
       (= A G)
       (not (= E 0))
       (= E F)
       (= C a!3)
       ((_ is O_TSLL) a!1)))))
      )
      (inv_main1017_4 C B A E)
    )
  )
)
(assert
  (forall ( (A Int) (B TSLL) (C Heap) (D Int) (E Int) (F Int) (G Int) (H Heap) ) 
    (=>
      (and
        (inv_main1001_2 H G F E)
        (let ((a!1 (HeapCtor (+ 1 (HeapSize H))
                     (store (HeapContents H) (+ 1 (HeapSize H)) (O_TSLL B)))))
  (and (= C a!1) (or (not (= D 0)) (= E 0)) (= A (+ 1 (HeapSize H)))))
      )
      (inv_main1007_3 C G F E A)
    )
  )
)
(assert
  (forall ( (A Int) (B TSLL) (C Heap) (D Heap) ) 
    (=>
      (and
        (inv_main996_2 D)
        (let ((a!1 (HeapCtor (+ 1 (HeapSize D))
                     (store (HeapContents D) (+ 1 (HeapSize D)) (O_TSLL B)))))
  (and (= C a!1) (= A (+ 1 (HeapSize D)))))
      )
      (inv_main996_2_1 C A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Heap) ) 
    (=>
      (and
        (inv_main_15 E D C B)
        (let ((a!1 (ite (and (not (<= C 0)) (>= (HeapSize E) C))
                (select (HeapContents E) C)
                defObj)))
  (and (= A (|TSLL::next| (getTSLL a!1))) ((_ is O_TSLL) a!1)))
      )
      (inv_main1027_9 E D C B A)
    )
  )
)
(assert
  (forall ( (A Heap) (B Int) (C Heap) ) 
    (=>
      (and
        (inv_main996_2_1 C B)
        (let ((a!1 (ite (and (not (<= B 0)) (>= (HeapSize C) B))
                (select (HeapContents C) B)
                defObj)))
(let ((a!2 (O_TSLL (TSLL 0 (|TSLL::data| (getTSLL a!1))))))
(let ((a!3 (ite (and (not (<= B 0)) (>= (HeapSize C) B))
                (HeapCtor (HeapSize C) (store (HeapContents C) B a!2))
                C)))
  (and (= A a!3) ((_ is O_TSLL) a!1)))))
      )
      (inv_main A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Heap) (v_5 Int) ) 
    (=>
      (and
        (inv_main_34 E D C B A)
        (and (not (= D 0)) (= C 0) (= v_5 D))
      )
      (inv_main_55 E D v_5 B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Heap) (E Int) (F Int) (G Int) (H Int) (I Int) (J Heap) (K Int) (L Int) (M Int) (N Int) (O Int) (P Heap) (v_16 Int) ) 
    (=>
      (and
        (inv_main_55 P O N M L)
        (let ((a!1 (ite (and (not (<= N 0)) (>= (HeapSize P) N))
                (select (HeapContents P) N)
                defObj))
      (a!2 (ite (and (not (<= I 0)) (>= (HeapSize J) I))
                (HeapCtor (HeapSize J) (store (HeapContents J) I defObj))
                J)))
  (and (= E (|TSLL::next| (getTSLL a!1)))
       (= C I)
       (= B G)
       (= A F)
       (= G M)
       (= F L)
       (not (= K 0))
       (= K E)
       (= I O)
       (= H N)
       (= D a!2)
       (= J P)
       ((_ is O_TSLL) a!1)
       (= v_16 K)))
      )
      (inv_main_55 D K v_16 B A)
    )
  )
)
(assert
  (forall ( (A Heap) (B Int) (C Int) (D Int) (E Heap) ) 
    (=>
      (and
        (inv_main1017_4 E D C B)
        (let ((a!1 (ite (and (not (<= C 0)) (>= (HeapSize E) C))
                (select (HeapContents E) C)
                defObj)))
(let ((a!2 (O_TSLL (TSLL (|TSLL::next| (getTSLL a!1)) 1))))
(let ((a!3 (ite (and (not (<= C 0)) (>= (HeapSize E) C))
                (HeapCtor (HeapSize E) (store (HeapContents E) C a!2))
                E)))
  (and (= A a!3) ((_ is O_TSLL) a!1)))))
      )
      (inv_main1001_2 A D C B)
    )
  )
)
(assert
  (forall ( (A Heap) (B Int) (C Int) (D Int) (E Heap) ) 
    (=>
      (and
        (inv_main1019_4 E D C B)
        (let ((a!1 (ite (and (not (<= C 0)) (>= (HeapSize E) C))
                (select (HeapContents E) C)
                defObj)))
(let ((a!2 (O_TSLL (TSLL (|TSLL::next| (getTSLL a!1)) 0))))
(let ((a!3 (ite (and (not (<= C 0)) (>= (HeapSize E) C))
                (HeapCtor (HeapSize E) (store (HeapContents E) C a!2))
                E)))
  (and (= A a!3) ((_ is O_TSLL) a!1)))))
      )
      (inv_main1001_2 A D C B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Heap) (D Int) (E Heap) (v_5 Int) ) 
    (=>
      (and
        (inv_main E D)
        (let ((a!1 (ite (and (not (<= D 0)) (>= (HeapSize E) D))
                (select (HeapContents E) D)
                defObj)))
(let ((a!2 (O_TSLL (TSLL (|TSLL::next| (getTSLL a!1)) 0))))
(let ((a!3 (ite (and (not (<= D 0)) (>= (HeapSize E) D))
                (HeapCtor (HeapSize E) (store (HeapContents E) D a!2))
                E)))
  (and (= B D) (= A 0) (= C a!3) ((_ is O_TSLL) a!1) (= v_5 B)))))
      )
      (inv_main1001_2 C B v_5 A)
    )
  )
)
(assert
  (forall ( (A Heap) (B Int) (C Int) (D Int) (E Int) (F Heap) ) 
    (=>
      (and
        (inv_main1007_3 F E D C B)
        (let ((a!1 (ite (and (not (<= D 0)) (>= (HeapSize F) D))
                (select (HeapContents F) D)
                defObj)))
(let ((a!2 (O_TSLL (TSLL B (|TSLL::data| (getTSLL a!1))))))
(let ((a!3 (ite (and (not (<= D 0)) (>= (HeapSize F) D))
                (HeapCtor (HeapSize F) (store (HeapContents F) D a!2))
                F)))
  (and (= A a!3) ((_ is O_TSLL) a!1)))))
      )
      (inv_main_5 A E D C)
    )
  )
)
(assert
  (forall ( (A Int) (B TSLL) (C Heap) (D Int) (E Int) (F Int) (G Heap) (H Int) (I Int) (J Int) (K Int) (L Heap) ) 
    (=>
      (and
        (inv_main_16 L K J I)
        (let ((a!1 (ite (and (not (<= J 0)) (>= (HeapSize L) J))
                (select (HeapContents L) J)
                defObj))
      (a!2 (HeapCtor (+ 1 (HeapSize G))
                     (store (HeapContents G) (+ 1 (HeapSize G)) (O_TSLL B)))))
  (and (= A (+ 1 (HeapSize G)))
       (= F K)
       (= E J)
       (= D I)
       (= H 0)
       (= H (|TSLL::next| (getTSLL a!1)))
       (= C a!2)
       (= G L)
       ((_ is O_TSLL) a!1)))
      )
      (inv_main1039_2 C F E D A)
    )
  )
)
(assert
  (forall ( (A Int) (B TSLL) (C Heap) (D Int) (E Int) (F Int) (G Heap) (H Int) (I Int) (J Int) (K Int) (L Int) (M Heap) ) 
    (=>
      (and
        (inv_main_16 M L K J)
        (let ((a!1 (ite (and (not (<= K 0)) (>= (HeapSize M) K))
                (select (HeapContents M) K)
                defObj))
      (a!2 (HeapCtor (+ 1 (HeapSize G))
                     (store (HeapContents G) (+ 1 (HeapSize G)) (O_TSLL B)))))
  (and (= A (+ 1 (HeapSize G)))
       (= D J)
       (not (= H 0))
       (= H (|TSLL::next| (getTSLL a!1)))
       (= F L)
       (= E K)
       (= I 0)
       (= C a!2)
       (= G M)
       ((_ is O_TSLL) a!1)))
      )
      (inv_main1039_2 C F E D A)
    )
  )
)
(assert
  (forall ( (A Heap) (B Int) (C Int) (D Int) (E Int) (F Int) (G Heap) ) 
    (=>
      (and
        (inv_main1046_3 G F E D C B)
        (let ((a!1 (ite (and (not (<= C 0)) (>= (HeapSize G) C))
                (select (HeapContents G) C)
                defObj)))
(let ((a!2 (O_TSLL (TSLL B (|TSLL::data| (getTSLL a!1))))))
(let ((a!3 (ite (and (not (<= C 0)) (>= (HeapSize G) C))
                (HeapCtor (HeapSize G) (store (HeapContents G) C a!2))
                G)))
  (and (= A a!3) ((_ is O_TSLL) a!1)))))
      )
      (inv_main_31 A F E D C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Heap) ) 
    (=>
      (and
        (inv_main1027_9 E D C B A)
        (= A 0)
      )
      (inv_main_16 E D C B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Heap) (E Int) (F Int) (G Int) (H Int) (I Heap) (J Int) (K Int) (L Int) (M Int) (N Int) (O Heap) ) 
    (=>
      (and
        (inv_main1027_9 O N M L K)
        (let ((a!1 (ite (and (not (<= M 0)) (>= (HeapSize O) M))
                (select (HeapContents O) M)
                defObj))
      (a!5 (or (and (= J 1) (= E 0)) (and (= J 0) (not (= E 0))))))
(let ((a!2 (not (<= (|TSLL::next| (getTSLL a!1)) 0))))
(let ((a!3 (and a!2 (>= (HeapSize O) (|TSLL::next| (getTSLL a!1))))))
(let ((a!4 (ite a!3
                (select (HeapContents O) (|TSLL::next| (getTSLL a!1)))
                defObj)))
  (and ((_ is O_TSLL) a!1)
       (= C H)
       (= B G)
       (= A F)
       (= F L)
       (= E (|TSLL::data| (getTSLL a!4)))
       (= J 0)
       (= H N)
       (= G M)
       (not (= K 0))
       (= D I)
       (= I O)
       a!5
       ((_ is O_TSLL) a!4))))))
      )
      (inv_main_16 D C B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Heap) (E Int) (F Int) (G Int) (H Int) (I Heap) ) 
    (=>
      (and
        (inv_main_25 I H G F)
        (let ((a!1 (ite (and (not (<= G 0)) (>= (HeapSize I) G))
                (select (HeapContents I) G)
                defObj)))
  (and (= C H)
       (= B G)
       (= A F)
       (= E 1)
       (= E (|TSLL::data| (getTSLL a!1)))
       (= D I)
       ((_ is O_TSLL) a!1)))
      )
      (inv_main_16 D C B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Heap) (G Int) (H Int) (I Int) (J Int) (K Heap) ) 
    (=>
      (and
        (inv_main_40 K J I H G)
        (let ((a!1 (ite (and (not (<= I 0)) (>= (HeapSize K) I))
                (select (HeapContents K) I)
                defObj)))
  (and (= E J)
       (= B G)
       (= A (|TSLL::next| (getTSLL a!1)))
       (= D I)
       (= C H)
       (= F K)
       ((_ is O_TSLL) a!1)))
      )
      (inv_main_33 F E A C B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Heap) (G Int) (H Int) (I Int) (J Int) (K Heap) (v_11 Int) ) 
    (=>
      (and
        (inv_main1043_3 K J I H G)
        (let ((a!1 (ite (and (not (<= I 0)) (>= (HeapSize K) I))
                (select (HeapContents K) I)
                defObj)))
(let ((a!2 (O_TSLL (TSLL G (|TSLL::data| (getTSLL a!1))))))
(let ((a!3 (ite (and (not (<= I 0)) (>= (HeapSize K) I))
                (HeapCtor (HeapSize K) (store (HeapContents K) I a!2))
                K)))
  (and (= E J)
       (= B G)
       (= A 0)
       (= D I)
       (= C H)
       (= F a!3)
       ((_ is O_TSLL) a!1)
       (= v_11 E)))))
      )
      (inv_main_33 F E v_11 A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Heap) (G Int) (H Int) (I Int) (J Int) (K Heap) (v_11 Int) ) 
    (=>
      (and
        (inv_main_31 K J I H G)
        (let ((a!1 (ite (and (not (<= I 0)) (>= (HeapSize K) I))
                (select (HeapContents K) I)
                defObj)))
(let ((a!2 (O_TSLL (TSLL G (|TSLL::data| (getTSLL a!1))))))
(let ((a!3 (ite (and (not (<= I 0)) (>= (HeapSize K) I))
                (HeapCtor (HeapSize K) (store (HeapContents K) I a!2))
                K)))
  (and (= E J)
       (= B G)
       (= A 0)
       (= D I)
       (= C H)
       (= F a!3)
       ((_ is O_TSLL) a!1)
       (= v_11 E)))))
      )
      (inv_main_33 F E v_11 A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Heap) (F Int) (G Int) (H Int) (I Int) (J Int) (K Heap) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Heap) ) 
    (=>
      (and
        (inv_main_33 Q P O N M)
        (let ((a!1 (ite (and (not (<= O 0)) (>= (HeapSize Q) O))
                (select (HeapContents Q) O)
                defObj))
      (a!2 (or (and (= L 0) (= F 1)) (and (= L 1) (not (= F 1))))))
  (and (= A G)
       (= F (|TSLL::data| (getTSLL a!1)))
       (= D J)
       (= C I)
       (= B H)
       (= H N)
       (= G M)
       (not (= L 0))
       (= J P)
       (= I O)
       (not (= O 0))
       (= E K)
       (= K Q)
       a!2
       ((_ is O_TSLL) a!1)))
      )
      (inv_main_35 E D C B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Heap) (F Int) (G Int) (H Int) (I Heap) ) 
    (=>
      (and
        (inv_main_23 I H G F)
        (let ((a!1 (ite (and (not (<= G 0)) (>= (HeapSize I) G))
                (select (HeapContents I) G)
                defObj)))
  (and (= C G)
       (= D H)
       (= B F)
       (= A (|TSLL::next| (getTSLL a!1)))
       (= E I)
       ((_ is O_TSLL) a!1)))
      )
      (inv_main_25 E D A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Heap) (G Int) (H Int) (I Int) (J Int) (K Heap) ) 
    (=>
      (and
        (inv_main_35 K J I H G)
        (let ((a!1 (ite (and (not (<= I 0)) (>= (HeapSize K) I))
                (select (HeapContents K) I)
                defObj)))
  (and (= E J)
       (= B G)
       (= A (|TSLL::data| (getTSLL a!1)))
       (= D I)
       (= C H)
       (= F K)
       ((_ is O_TSLL) a!1)))
      )
      (inv_main_36 F E D A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Heap) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Heap) ) 
    (=>
      (and
        (inv_main_36 K J I H G)
        (let ((a!1 (ite (and (not (<= I 0)) (>= (HeapSize K) I))
                (select (HeapContents K) I)
                defObj)))
  (and (= E 0)
       (= E (|TSLL::data| (getTSLL a!1)))
       (= B I)
       (= A G)
       (= F 0)
       (= F H)
       (= C J)
       (= D K)
       ((_ is O_TSLL) a!1)))
      )
      (inv_main_40 D C B F A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Heap) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Heap) ) 
    (=>
      (and
        (inv_main_45 K J I H G)
        (let ((a!1 (ite (and (not (<= I 0)) (>= (HeapSize K) I))
                (select (HeapContents K) I)
                defObj)))
  (and (= E 1)
       (= E (|TSLL::data| (getTSLL a!1)))
       (= B I)
       (= A G)
       (= F 1)
       (= F H)
       (= C J)
       (= D K)
       ((_ is O_TSLL) a!1)))
      )
      (inv_main_49 D C B F A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Heap) (E Int) (F Int) (G Int) (H Int) (I Int) (J Heap) ) 
    (=>
      (and
        (inv_main_16 J I H G)
        (let ((a!1 (ite (and (not (<= H 0)) (>= (HeapSize J) H))
                (select (HeapContents J) H)
                defObj)))
  (and (= A G)
       (not (= E 0))
       (= E (|TSLL::next| (getTSLL a!1)))
       (= C I)
       (= B H)
       (not (= F 0))
       (= D J)
       ((_ is O_TSLL) a!1)))
      )
      (inv_main_23 D C B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Heap) (E Int) (F Int) (G Int) (H Int) (I Heap) (J Int) (K Int) (L Int) (M Int) (N Int) (O Heap) ) 
    (=>
      (and
        (inv_main1027_9 O N M L K)
        (let ((a!1 (ite (and (not (<= M 0)) (>= (HeapSize O) M))
                (select (HeapContents O) M)
                defObj))
      (a!5 (or (and (= J 1) (= E 0)) (and (= J 0) (not (= E 0))))))
(let ((a!2 (not (<= (|TSLL::next| (getTSLL a!1)) 0))))
(let ((a!3 (and a!2 (>= (HeapSize O) (|TSLL::next| (getTSLL a!1))))))
(let ((a!4 (ite a!3
                (select (HeapContents O) (|TSLL::next| (getTSLL a!1)))
                defObj)))
  (and ((_ is O_TSLL) a!1)
       (= C H)
       (= B G)
       (= A F)
       (= F L)
       (= E (|TSLL::data| (getTSLL a!4)))
       (not (= J 0))
       (= H N)
       (= G M)
       (not (= K 0))
       (= D I)
       (= I O)
       a!5
       ((_ is O_TSLL) a!4))))))
      )
      (inv_main_17 D C B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Heap) (F Int) (G Int) (H Int) (I Heap) ) 
    (=>
      (and
        (inv_main_19 I H G F)
        (let ((a!1 (ite (and (not (<= G 0)) (>= (HeapSize I) G))
                (select (HeapContents I) G)
                defObj)))
  (and (= C G)
       (= D H)
       (= B F)
       (= A (|TSLL::next| (getTSLL a!1)))
       (= E I)
       ((_ is O_TSLL) a!1)))
      )
      (inv_main_15 E D A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Heap) (v_6 Int) ) 
    (=>
      (and
        (inv_main1001_2 F E D C)
        (and (= A 0) (not (= C 0)) (= B 0) (not (= 0 E)) (= v_6 E))
      )
      (inv_main_15 F E v_6 A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Heap) (F Int) (G Int) (H Int) (I Heap) ) 
    (=>
      (and
        (inv_main_5 I H G F)
        (let ((a!1 (ite (and (not (<= G 0)) (>= (HeapSize I) G))
                (select (HeapContents I) G)
                defObj)))
  (and (= C G)
       (= D H)
       (= B F)
       (= A (|TSLL::next| (getTSLL a!1)))
       (= E I)
       ((_ is O_TSLL) a!1)))
      )
      (inv_main_6 E D A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Heap) (G Int) (H Int) (I Int) (J Int) (K Heap) ) 
    (=>
      (and
        (inv_main_44 K J I H G)
        (let ((a!1 (ite (and (not (<= I 0)) (>= (HeapSize K) I))
                (select (HeapContents K) I)
                defObj)))
  (and (= E J)
       (= B G)
       (= A (|TSLL::data| (getTSLL a!1)))
       (= D I)
       (= C H)
       (= F K)
       ((_ is O_TSLL) a!1)))
      )
      (inv_main_45 F E D A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Heap) (G Int) (H Int) (I Int) (J Int) (K Heap) ) 
    (=>
      (and
        (inv_main_49 K J I H G)
        (let ((a!1 (ite (and (not (<= I 0)) (>= (HeapSize K) I))
                (select (HeapContents K) I)
                defObj)))
  (and (= E J)
       (= B G)
       (= A (|TSLL::next| (getTSLL a!1)))
       (= D I)
       (= C H)
       (= F K)
       ((_ is O_TSLL) a!1)))
      )
      (inv_main_34 F E A C B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Heap) ) 
    (=>
      (and
        (inv_main_33 E D C B A)
        (= C 0)
      )
      (inv_main_34 E D C B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Heap) (F Int) (G Int) (H Int) (I Int) (J Int) (K Heap) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Heap) ) 
    (=>
      (and
        (inv_main_33 Q P O N M)
        (let ((a!1 (ite (and (not (<= O 0)) (>= (HeapSize Q) O))
                (select (HeapContents Q) O)
                defObj))
      (a!2 (or (and (= L 0) (= F 1)) (and (= L 1) (not (= F 1))))))
  (and (= A G)
       (= F (|TSLL::data| (getTSLL a!1)))
       (= D J)
       (= C I)
       (= B H)
       (= H N)
       (= G M)
       (= L 0)
       (= J P)
       (= I O)
       (not (= O 0))
       (= E K)
       (= K Q)
       a!2
       ((_ is O_TSLL) a!1)))
      )
      (inv_main_34 E D C B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Heap) ) 
    (=>
      (and
        (inv_main_34 E D C B A)
        (not (= C 0))
      )
      (inv_main_44 E D C B A)
    )
  )
)
(assert
  (forall ( (A Heap) (B Int) (C Int) (D Int) (E Int) (F Heap) ) 
    (=>
      (and
        (inv_main1039_2 F E D C B)
        (let ((a!1 (ite (and (not (<= B 0)) (>= (HeapSize F) B))
                (select (HeapContents F) B)
                defObj)))
(let ((a!2 (O_TSLL (TSLL (|TSLL::next| (getTSLL a!1)) 1))))
(let ((a!3 (ite (and (not (<= B 0)) (>= (HeapSize F) B))
                (HeapCtor (HeapSize F) (store (HeapContents F) B a!2))
                F)))
  (and (= A a!3) ((_ is O_TSLL) a!1)))))
      )
      (inv_main_28 A E D C B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Heap) (F Int) (G Int) (H Int) (I Int) (J Int) (K Heap) ) 
    (=>
      (and
        (inv_main_29 K J I H G)
        (let ((a!1 (ite (and (not (<= I 0)) (>= (HeapSize K) I))
                (select (HeapContents K) I)
                defObj)))
  (and (= B H)
       (= A G)
       (= F 0)
       (= F (|TSLL::next| (getTSLL a!1)))
       (= D J)
       (= C I)
       (= E K)
       ((_ is O_TSLL) a!1)))
      )
      (inv_main1043_3 E D C B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Heap) ) 
    (=>
      (and
        (inv_main996_2_1 B A)
        (let ((a!1 (ite (and (not (<= A 0)) (>= (HeapSize B) A))
                (select (HeapContents B) A)
                defObj)))
  (not ((_ is O_TSLL) a!1)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Heap) ) 
    (=>
      (and
        (inv_main B A)
        (let ((a!1 (ite (and (not (<= A 0)) (>= (HeapSize B) A))
                (select (HeapContents B) A)
                defObj)))
  (not ((_ is O_TSLL) a!1)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Heap) ) 
    (=>
      (and
        (inv_main1007_3 E D C B A)
        (let ((a!1 (ite (and (not (<= C 0)) (>= (HeapSize E) C))
                (select (HeapContents E) C)
                defObj)))
  (not ((_ is O_TSLL) a!1)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Heap) ) 
    (=>
      (and
        (inv_main_5 D C B A)
        (let ((a!1 (ite (and (not (<= B 0)) (>= (HeapSize D) B))
                (select (HeapContents D) B)
                defObj)))
  (not ((_ is O_TSLL) a!1)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Heap) ) 
    (=>
      (and
        (inv_main_6 D C B A)
        (let ((a!1 (ite (and (not (<= B 0)) (>= (HeapSize D) B))
                (select (HeapContents D) B)
                defObj)))
  (not ((_ is O_TSLL) a!1)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Heap) ) 
    (=>
      (and
        (inv_main1017_4 D C B A)
        (let ((a!1 (ite (and (not (<= B 0)) (>= (HeapSize D) B))
                (select (HeapContents D) B)
                defObj)))
  (not ((_ is O_TSLL) a!1)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Heap) ) 
    (=>
      (and
        (inv_main1019_4 D C B A)
        (let ((a!1 (ite (and (not (<= B 0)) (>= (HeapSize D) B))
                (select (HeapContents D) B)
                defObj)))
  (not ((_ is O_TSLL) a!1)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Heap) ) 
    (=>
      (and
        (inv_main_15 D C B A)
        (let ((a!1 (ite (and (not (<= B 0)) (>= (HeapSize D) B))
                (select (HeapContents D) B)
                defObj)))
  (not ((_ is O_TSLL) a!1)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Heap) ) 
    (=>
      (and
        (inv_main1027_9 E D C B A)
        (let ((a!1 (ite (and (not (<= C 0)) (>= (HeapSize E) C))
                (select (HeapContents E) C)
                defObj)))
  (and (not (= A 0)) (not ((_ is O_TSLL) a!1))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Heap) ) 
    (=>
      (and
        (inv_main1027_9 E D C B A)
        (let ((a!1 (ite (and (not (<= C 0)) (>= (HeapSize E) C))
                (select (HeapContents E) C)
                defObj)))
(let ((a!2 (not (<= (|TSLL::next| (getTSLL a!1)) 0))))
(let ((a!3 (and a!2 (>= (HeapSize E) (|TSLL::next| (getTSLL a!1))))))
(let ((a!4 (ite a!3
                (select (HeapContents E) (|TSLL::next| (getTSLL a!1)))
                defObj)))
  (and ((_ is O_TSLL) a!1) (not (= A 0)) (not ((_ is O_TSLL) a!4)))))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Heap) ) 
    (=>
      (and
        (inv_main_17 D C B A)
        (let ((a!1 (ite (and (not (<= B 0)) (>= (HeapSize D) B))
                (select (HeapContents D) B)
                defObj)))
  (not ((_ is O_TSLL) a!1)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Heap) ) 
    (=>
      (and
        (inv_main_19 D C B A)
        (let ((a!1 (ite (and (not (<= B 0)) (>= (HeapSize D) B))
                (select (HeapContents D) B)
                defObj)))
  (not ((_ is O_TSLL) a!1)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Heap) ) 
    (=>
      (and
        (inv_main_16 D C B A)
        (let ((a!1 (ite (and (not (<= B 0)) (>= (HeapSize D) B))
                (select (HeapContents D) B)
                defObj)))
  (not ((_ is O_TSLL) a!1)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Heap) ) 
    (=>
      (and
        (inv_main_23 D C B A)
        (let ((a!1 (ite (and (not (<= B 0)) (>= (HeapSize D) B))
                (select (HeapContents D) B)
                defObj)))
  (not ((_ is O_TSLL) a!1)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Heap) ) 
    (=>
      (and
        (inv_main_25 D C B A)
        (let ((a!1 (ite (and (not (<= B 0)) (>= (HeapSize D) B))
                (select (HeapContents D) B)
                defObj)))
  (not ((_ is O_TSLL) a!1)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Heap) ) 
    (=>
      (and
        (inv_main1039_2 E D C B A)
        (let ((a!1 (ite (and (not (<= A 0)) (>= (HeapSize E) A))
                (select (HeapContents E) A)
                defObj)))
  (not ((_ is O_TSLL) a!1)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Heap) ) 
    (=>
      (and
        (inv_main_28 E D C B A)
        (let ((a!1 (ite (and (not (<= A 0)) (>= (HeapSize E) A))
                (select (HeapContents E) A)
                defObj)))
  (not ((_ is O_TSLL) a!1)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Heap) ) 
    (=>
      (and
        (inv_main_29 E D C B A)
        (let ((a!1 (ite (and (not (<= C 0)) (>= (HeapSize E) C))
                (select (HeapContents E) C)
                defObj)))
  (not ((_ is O_TSLL) a!1)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Heap) ) 
    (=>
      (and
        (inv_main1043_3 E D C B A)
        (let ((a!1 (ite (and (not (<= C 0)) (>= (HeapSize E) C))
                (select (HeapContents E) C)
                defObj)))
  (not ((_ is O_TSLL) a!1)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Heap) ) 
    (=>
      (and
        (inv_main1045_2 E D C B A)
        (let ((a!1 (ite (and (not (<= C 0)) (>= (HeapSize E) C))
                (select (HeapContents E) C)
                defObj)))
  (not ((_ is O_TSLL) a!1)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Heap) ) 
    (=>
      (and
        (inv_main1046_3 F E D C B A)
        (let ((a!1 (ite (and (not (<= B 0)) (>= (HeapSize F) B))
                (select (HeapContents F) B)
                defObj)))
  (not ((_ is O_TSLL) a!1)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Heap) ) 
    (=>
      (and
        (inv_main_31 E D C B A)
        (let ((a!1 (ite (and (not (<= C 0)) (>= (HeapSize E) C))
                (select (HeapContents E) C)
                defObj)))
  (not ((_ is O_TSLL) a!1)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Heap) ) 
    (=>
      (and
        (inv_main_33 E D C B A)
        (let ((a!1 (ite (and (not (<= C 0)) (>= (HeapSize E) C))
                (select (HeapContents E) C)
                defObj)))
  (and (not (= C 0)) (not ((_ is O_TSLL) a!1))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Heap) ) 
    (=>
      (and
        (inv_main_35 E D C B A)
        (let ((a!1 (ite (and (not (<= C 0)) (>= (HeapSize E) C))
                (select (HeapContents E) C)
                defObj)))
  (not ((_ is O_TSLL) a!1)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Heap) ) 
    (=>
      (and
        (inv_main_36 E D C B A)
        (let ((a!1 (ite (and (not (<= C 0)) (>= (HeapSize E) C))
                (select (HeapContents E) C)
                defObj)))
  (not ((_ is O_TSLL) a!1)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Heap) ) 
    (=>
      (and
        (inv_main_40 E D C B A)
        (let ((a!1 (ite (and (not (<= C 0)) (>= (HeapSize E) C))
                (select (HeapContents E) C)
                defObj)))
  (not ((_ is O_TSLL) a!1)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Heap) ) 
    (=>
      (and
        (inv_main_44 E D C B A)
        (let ((a!1 (ite (and (not (<= C 0)) (>= (HeapSize E) C))
                (select (HeapContents E) C)
                defObj)))
  (not ((_ is O_TSLL) a!1)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Heap) ) 
    (=>
      (and
        (inv_main_45 E D C B A)
        (let ((a!1 (ite (and (not (<= C 0)) (>= (HeapSize E) C))
                (select (HeapContents E) C)
                defObj)))
  (not ((_ is O_TSLL) a!1)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Heap) ) 
    (=>
      (and
        (inv_main_49 E D C B A)
        (let ((a!1 (ite (and (not (<= C 0)) (>= (HeapSize E) C))
                (select (HeapContents E) C)
                defObj)))
  (not ((_ is O_TSLL) a!1)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Heap) ) 
    (=>
      (and
        (inv_main_55 E D C B A)
        (let ((a!1 (ite (and (not (<= C 0)) (>= (HeapSize E) C))
                (select (HeapContents E) C)
                defObj)))
  (not ((_ is O_TSLL) a!1)))
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

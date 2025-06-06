(set-logic HORN)

(declare-datatypes ((|node| 0)) (((|node|  (|node::h| Int) (|node::n| Int)))))
(declare-datatypes ((|HeapObject| 0) (|AddrRange| 0)) (((|O_Int|  (|getInt| Int)) (|O_UInt|  (|getUInt| Int)) (|O_Addr|  (|getAddr| Int)) (|O_AddrRange|  (|getAddrRange| AddrRange)) (|O_node|  (|getnode| node)) (|defObj| ))
                                                   ((|AddrRange|  (|AddrRangeStart| Int) (|AddrRangeSize| Int)))))
(declare-datatypes ((|Heap| 0)) (((|HeapCtor|  (|HeapSize| Int) (|HeapContents| (Array Int HeapObject))))))

(declare-fun |inv_main551_5_17| ( Heap Int Int Int Int ) Bool)
(declare-fun |inv_main532_3| ( Heap ) Bool)
(declare-fun |inv_main554_5_18| ( Heap Int Int Int Int ) Bool)
(declare-fun |inv_main538_15| ( Heap Int Int Int Int ) Bool)
(declare-fun |inv_main540_12| ( Heap Int Int Int Int ) Bool)
(declare-fun |inv_main_4| ( Heap Int Int Int Int ) Bool)
(declare-fun |inv_main551_5| ( Heap Int Int Int Int ) Bool)
(declare-fun |inv_main_16| ( Heap Int Int Int Int ) Bool)
(declare-fun |inv_main554_5| ( Heap Int Int Int Int ) Bool)
(declare-fun |inv_main_13| ( Heap Int Int Int Int ) Bool)
(declare-fun |CHC_COMP_FALSE| ( ) Bool)
(declare-fun |inv_main_5| ( Heap Int Int Int Int ) Bool)
(declare-fun |inv_main_9| ( Heap Int Int Int Int ) Bool)

(assert
  (forall ( (A Heap) ) 
    (=>
      (and
        (= A (HeapCtor 0 ((as const (Array Int HeapObject)) defObj)))
      )
      (inv_main532_3 A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Heap) ) 
    (=>
      (and
        (inv_main_4 F E D C B)
        (and (= E 0) (not (= A 0)))
      )
      (inv_main540_12 F E D C B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Heap) ) 
    (=>
      (and
        (inv_main_4 F E D C B)
        (and (not (= E 0)) (not (= A 0)))
      )
      (inv_main538_15 F E D C B)
    )
  )
)
(assert
  (forall ( (A Heap) (B Int) (C Int) (D Int) (E Int) (F Heap) ) 
    (=>
      (and
        (inv_main_9 F E D C B)
        (let ((a!1 (ite (and (not (<= D 0)) (>= (HeapSize F) D))
                (select (HeapContents F) D)
                defObj)))
(let ((a!2 (O_node (node (|node::h| (getnode a!1)) B))))
(let ((a!3 (ite (and (not (<= D 0)) (>= (HeapSize F) D))
                (HeapCtor (HeapSize F) (store (HeapContents F) D a!2))
                F)))
  (and (= A a!3) ((_ is O_node) a!1)))))
      )
      (inv_main_13 A E D C B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Heap) (F Int) (G Int) (H Int) (I Int) (J Int) (K Heap) ) 
    (=>
      (and
        (inv_main551_5 K J I H G)
        (let ((a!1 (ite (and (not (<= I 0)) (>= (HeapSize K) I))
                (select (HeapContents K) I)
                defObj)))
  (and (= D J)
       (= C I)
       (= B H)
       (= A G)
       (not (= F 1))
       (= F (|node::h| (getnode a!1)))
       (= E K)
       ((_ is O_node) a!1)))
      )
      (inv_main_16 E D C B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Heap) (F Int) (G Int) (H Int) (I Int) (J Int) (K Heap) ) 
    (=>
      (and
        (inv_main554_5 K J I H G)
        (let ((a!1 (ite (and (not (<= I 0)) (>= (HeapSize K) I))
                (select (HeapContents K) I)
                defObj)))
  (and (= D J)
       (= C I)
       (= B H)
       (= A G)
       (not (= F 2))
       (= F (|node::h| (getnode a!1)))
       (= E K)
       ((_ is O_node) a!1)))
      )
      (inv_main_16 E D C B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I node) (J Heap) (K Heap) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Heap) ) 
    (=>
      (and
        (inv_main538_15 Q P O N M)
        (let ((a!1 (HeapCtor (+ 1 (HeapSize J))
                     (store (HeapContents J) (+ 1 (HeapSize J)) (O_node I))))
      (a!2 (ite (and (not (<= O 0)) (>= (HeapSize Q) O))
                (select (HeapContents Q) O)
                defObj)))
(let ((a!3 (O_node (node 1 (|node::n| (getnode a!2))))))
(let ((a!4 (ite (and (not (<= O 0)) (>= (HeapSize Q) O))
                (HeapCtor (HeapSize Q) (store (HeapContents Q) O a!3))
                Q)))
  (and (= H G)
       (= G P)
       (= F E)
       (= E O)
       (= D C)
       (= C N)
       (= B A)
       (= A M)
       (not (= L 0))
       (= L (+ 1 (HeapSize J)))
       (= K a!1)
       (= J a!4)
       ((_ is O_node) a!2)))))
      )
      (inv_main_9 K H F D L)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I node) (J Heap) (K Heap) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Heap) ) 
    (=>
      (and
        (inv_main540_12 Q P O N M)
        (let ((a!1 (HeapCtor (+ 1 (HeapSize J))
                     (store (HeapContents J) (+ 1 (HeapSize J)) (O_node I))))
      (a!2 (ite (and (not (<= O 0)) (>= (HeapSize Q) O))
                (select (HeapContents Q) O)
                defObj)))
(let ((a!3 (O_node (node 2 (|node::n| (getnode a!2))))))
(let ((a!4 (ite (and (not (<= O 0)) (>= (HeapSize Q) O))
                (HeapCtor (HeapSize Q) (store (HeapContents Q) O a!3))
                Q)))
  (and (= H G)
       (= G P)
       (= F E)
       (= E O)
       (= D C)
       (= C N)
       (= B A)
       (= A M)
       (not (= L 0))
       (= L (+ 1 (HeapSize J)))
       (= K a!1)
       (= J a!4)
       ((_ is O_node) a!2)))))
      )
      (inv_main_9 K H F D L)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Heap) (F Int) (G Int) (H Int) (I Int) (J Int) (K Heap) ) 
    (=>
      (and
        (inv_main554_5 K J I H G)
        (let ((a!1 (ite (and (not (<= I 0)) (>= (HeapSize K) I))
                (select (HeapContents K) I)
                defObj)))
  (and (= D J)
       (= C I)
       (= B H)
       (= A G)
       (= F 2)
       (= F (|node::h| (getnode a!1)))
       (= E K)
       ((_ is O_node) a!1)))
      )
      (inv_main554_5_18 E D C B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Heap) (G Int) (H Int) (I Int) (J Int) (K Heap) ) 
    (=>
      (and
        (inv_main_13 K J I H G)
        (let ((a!1 (ite (and (not (<= I 0)) (>= (HeapSize K) I))
                (select (HeapContents K) I)
                defObj)))
  (and (= E J)
       (= D I)
       (= C H)
       (= B G)
       (= A (|node::n| (getnode a!1)))
       (= F K)
       ((_ is O_node) a!1)))
      )
      (inv_main_4 F E A C B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I node) (J Heap) (K Int) (L Heap) (v_12 Int) ) 
    (=>
      (and
        (inv_main532_3 L)
        (let ((a!1 (HeapCtor (+ 1 (HeapSize L))
                     (store (HeapContents L) (+ 1 (HeapSize L)) (O_node I)))))
  (and (= D C)
       (= B A)
       (= H G)
       (not (= K 0))
       (= K (+ 1 (HeapSize L)))
       (= J a!1)
       (= F E)
       (= v_12 K)))
      )
      (inv_main_4 J H K v_12 B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Heap) (G Int) (H Int) (I Int) (J Int) (K Heap) ) 
    (=>
      (and
        (inv_main551_5_17 K J I H G)
        (let ((a!1 (ite (and (not (<= I 0)) (>= (HeapSize K) I))
                (select (HeapContents K) I)
                defObj)))
  (and (= E J)
       (= D I)
       (= C H)
       (= B G)
       (= A (|node::n| (getnode a!1)))
       (= F K)
       ((_ is O_node) a!1)))
      )
      (inv_main551_5 F E A C B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Heap) (E Int) (F Int) (G Int) (H Int) (I Int) (J Heap) (v_10 Int) ) 
    (=>
      (and
        (inv_main_5 J I H G F)
        (let ((a!1 (ite (and (not (<= H 0)) (>= (HeapSize J) H))
                (select (HeapContents J) H)
                defObj)))
(let ((a!2 (O_node (node 3 (|node::n| (getnode a!1))))))
(let ((a!3 (ite (and (not (<= H 0)) (>= (HeapSize J) H))
                (HeapCtor (HeapSize J) (store (HeapContents J) H a!2))
                J)))
  (and (= C H)
       (= B G)
       (= A F)
       (not (= E 0))
       (= E I)
       (= D a!3)
       ((_ is O_node) a!1)
       (= v_10 B)))))
      )
      (inv_main551_5 D E B v_10 A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Heap) (G Int) (H Int) (I Int) (J Int) (K Heap) ) 
    (=>
      (and
        (inv_main554_5_18 K J I H G)
        (let ((a!1 (ite (and (not (<= I 0)) (>= (HeapSize K) I))
                (select (HeapContents K) I)
                defObj)))
  (and (= E J)
       (= D I)
       (= C H)
       (= B G)
       (= A (|node::n| (getnode a!1)))
       (= F K)
       ((_ is O_node) a!1)))
      )
      (inv_main554_5 F E A C B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Heap) (E Int) (F Int) (G Int) (H Int) (I Int) (J Heap) (v_10 Int) ) 
    (=>
      (and
        (inv_main_5 J I H G F)
        (let ((a!1 (ite (and (not (<= H 0)) (>= (HeapSize J) H))
                (select (HeapContents J) H)
                defObj)))
(let ((a!2 (O_node (node 3 (|node::n| (getnode a!1))))))
(let ((a!3 (ite (and (not (<= H 0)) (>= (HeapSize J) H))
                (HeapCtor (HeapSize J) (store (HeapContents J) H a!2))
                J)))
  (and (= C H)
       (= B G)
       (= A F)
       (= E 0)
       (= E I)
       (= D a!3)
       ((_ is O_node) a!1)
       (= v_10 B)))))
      )
      (inv_main554_5 D E B v_10 A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Heap) ) 
    (=>
      (and
        (inv_main_4 F E D C B)
        (= A 0)
      )
      (inv_main_5 F E D C B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Heap) (F Int) (G Int) (H Int) (I Int) (J Int) (K Heap) ) 
    (=>
      (and
        (inv_main551_5 K J I H G)
        (let ((a!1 (ite (and (not (<= I 0)) (>= (HeapSize K) I))
                (select (HeapContents K) I)
                defObj)))
  (and (= D J)
       (= C I)
       (= B H)
       (= A G)
       (= F 1)
       (= F (|node::h| (getnode a!1)))
       (= E K)
       ((_ is O_node) a!1)))
      )
      (inv_main551_5_17 E D C B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Heap) ) 
    (=>
      (and
        (inv_main538_15 E D C B A)
        (let ((a!1 (ite (and (not (<= C 0)) (>= (HeapSize E) C))
                (select (HeapContents E) C)
                defObj)))
  (not ((_ is O_node) a!1)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Heap) ) 
    (=>
      (and
        (inv_main540_12 E D C B A)
        (let ((a!1 (ite (and (not (<= C 0)) (>= (HeapSize E) C))
                (select (HeapContents E) C)
                defObj)))
  (not ((_ is O_node) a!1)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Heap) ) 
    (=>
      (and
        (inv_main_9 E D C B A)
        (let ((a!1 (ite (and (not (<= C 0)) (>= (HeapSize E) C))
                (select (HeapContents E) C)
                defObj)))
  (not ((_ is O_node) a!1)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Heap) ) 
    (=>
      (and
        (inv_main_13 E D C B A)
        (let ((a!1 (ite (and (not (<= C 0)) (>= (HeapSize E) C))
                (select (HeapContents E) C)
                defObj)))
  (not ((_ is O_node) a!1)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Heap) ) 
    (=>
      (and
        (inv_main_5 E D C B A)
        (let ((a!1 (ite (and (not (<= C 0)) (>= (HeapSize E) C))
                (select (HeapContents E) C)
                defObj)))
  (not ((_ is O_node) a!1)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Heap) ) 
    (=>
      (and
        (inv_main551_5 E D C B A)
        (let ((a!1 (ite (and (not (<= C 0)) (>= (HeapSize E) C))
                (select (HeapContents E) C)
                defObj)))
  (not ((_ is O_node) a!1)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Heap) ) 
    (=>
      (and
        (inv_main551_5_17 E D C B A)
        (let ((a!1 (ite (and (not (<= C 0)) (>= (HeapSize E) C))
                (select (HeapContents E) C)
                defObj)))
  (not ((_ is O_node) a!1)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Heap) ) 
    (=>
      (and
        (inv_main554_5 E D C B A)
        (let ((a!1 (ite (and (not (<= C 0)) (>= (HeapSize E) C))
                (select (HeapContents E) C)
                defObj)))
  (not ((_ is O_node) a!1)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Heap) ) 
    (=>
      (and
        (inv_main554_5_18 E D C B A)
        (let ((a!1 (ite (and (not (<= C 0)) (>= (HeapSize E) C))
                (select (HeapContents E) C)
                defObj)))
  (not ((_ is O_node) a!1)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Heap) ) 
    (=>
      (and
        (inv_main_16 E D C B A)
        (let ((a!1 (ite (and (not (<= C 0)) (>= (HeapSize E) C))
                (select (HeapContents E) C)
                defObj)))
  (not ((_ is O_node) a!1)))
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

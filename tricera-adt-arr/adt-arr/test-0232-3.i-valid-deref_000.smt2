(set-logic HORN)

(declare-datatypes ((|item| 0)) (((|item|  (|item::next| Int) (|item::data| Int)))))
(declare-datatypes ((|HeapObject| 0) (|AddrRange| 0)) (((|O_Int|  (|getInt| Int)) (|O_UInt|  (|getUInt| Int)) (|O_Addr|  (|getAddr| Int)) (|O_AddrRange|  (|getAddrRange| AddrRange)) (|O_item|  (|getitem| item)) (|defObj| ))
                                                   ((|AddrRange|  (|AddrRangeStart| Int) (|AddrRangeSize| Int)))))
(declare-datatypes ((|Heap| 0)) (((|HeapCtor|  (|HeapSize| Int) (|HeapContents| (Array Int HeapObject))))))

(declare-fun |inv_main530_5| ( Heap Int Int Int ) Bool)
(declare-fun |inv_main543_9| ( Heap Int ) Bool)
(declare-fun |inv_main532_18| ( Heap Int Int Int Int ) Bool)
(declare-fun |inv_main539_5| ( Heap ) Bool)
(declare-fun |inv_main_3| ( Heap Int Int Int ) Bool)
(declare-fun |inv_main551_13| ( Heap Int Int ) Bool)
(declare-fun |inv_main544_9| ( Heap Int Int ) Bool)
(declare-fun |CHC_COMP_FALSE| ( ) Bool)
(declare-fun |inv_main_10| ( Heap Int ) Bool)

(assert
  (forall ( (A Heap) ) 
    (=>
      (and
        (= A (HeapCtor 0 ((as const (Array Int HeapObject)) defObj)))
      )
      (inv_main539_5 A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Heap) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Heap) ) 
    (=>
      (and
        (inv_main532_18 J I H G F)
        (let ((a!1 (ite (and (not (<= G 0)) (>= (HeapSize J) G))
                (select (HeapContents J) G)
                defObj)))
(let ((a!2 (O_item (item (|item::next| (getitem a!1)) F))))
(let ((a!3 (ite (and (not (<= G 0)) (>= (HeapSize J) G))
                (HeapCtor (HeapSize J) (store (HeapContents J) G a!2))
                J)))
  (and (not (= E 0))
       (= E G)
       (= D 0)
       (= B I)
       (= A H)
       (= C a!3)
       ((_ is O_item) a!1)))))
      )
      (inv_main543_9 C E)
    )
  )
)
(assert
  (forall ( (A Int) (B Heap) (C Int) (D Int) (E Heap) ) 
    (=>
      (and
        (inv_main_10 E D)
        (let ((a!1 (ite (and (not (<= D 0)) (>= (HeapSize E) D))
                (select (HeapContents E) D)
                defObj)))
  (and (= C 0)
       (= C (|item::next| (getitem a!1)))
       (= A D)
       (= B E)
       ((_ is O_item) a!1)))
      )
      (inv_main551_13 B A C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Heap) ) 
    (=>
      (and
        (inv_main_3 E D C B)
        (let ((a!1 (ite (and (not (<= B 0)) (>= (HeapSize E) B))
                (select (HeapContents E) B)
                defObj)))
(let ((a!2 (not (= (|item::next| (getitem a!1)) 0)))
      (a!3 (not (<= (|item::next| (getitem a!1)) 0))))
(let ((a!4 (and a!3 (>= (HeapSize E) (|item::next| (getitem a!1))))))
(let ((a!5 (ite a!4
                (select (HeapContents E) (|item::next| (getitem a!1)))
                defObj)))
  (and ((_ is O_item) a!1)
       a!2
       (= A (|item::data| (getitem a!5)))
       ((_ is O_item) a!5))))))
      )
      (inv_main532_18 E D C B A)
    )
  )
)
(assert
  (forall ( (A Int) (B item) (C Heap) (D Int) (E Int) (F Int) (G Heap) ) 
    (=>
      (and
        (inv_main_3 G F E D)
        (let ((a!1 (ite (and (not (<= D 0)) (>= (HeapSize G) D))
                (select (HeapContents G) D)
                defObj))
      (a!2 (HeapCtor (+ 1 (HeapSize G))
                     (store (HeapContents G) (+ 1 (HeapSize G)) (O_item B)))))
  (and (= (|item::next| (getitem a!1)) 0)
       (= A (+ 1 (HeapSize G)))
       (= C a!2)
       ((_ is O_item) a!1)))
      )
      (inv_main532_18 C F E D A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C item) (D Heap) (E Int) (F Heap) (G Heap) ) 
    (=>
      (and
        (inv_main539_5 G)
        (let ((a!1 (HeapCtor (+ 1 (HeapSize F))
                     (store (HeapContents F) (+ 1 (HeapSize F)) (O_item C)))))
  (and (= B 1) (= A (+ 1 (HeapSize F))) (= D a!1) (= F G) (= E 0)))
      )
      (inv_main530_5 D E B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C item) (D Heap) (E Int) (F Int) (G Int) (H Heap) (I Int) (J Int) (K Int) (L Int) (M Int) (N Heap) ) 
    (=>
      (and
        (inv_main532_18 N M L K J)
        (let ((a!1 (ite (and (not (<= K 0)) (>= (HeapSize N) K))
                (select (HeapContents N) K)
                defObj))
      (a!4 (HeapCtor (+ 1 (HeapSize H))
                     (store (HeapContents H) (+ 1 (HeapSize H)) (O_item C)))))
(let ((a!2 (O_item (item (|item::next| (getitem a!1)) J))))
(let ((a!3 (ite (and (not (<= K 0)) (>= (HeapSize N) K))
                (HeapCtor (HeapSize N) (store (HeapContents N) K a!2))
                N)))
  (and (= G M)
       (= B 1)
       (= A (+ 1 (HeapSize H)))
       (not (= I 0))
       (= F L)
       (= E K)
       (= H a!3)
       (= D a!4)
       ((_ is O_item) a!1)))))
      )
      (inv_main530_5 D E B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Heap) ) 
    (=>
      (and
        (inv_main543_9 C B)
        (let ((a!1 (ite (and (not (<= B 0)) (>= (HeapSize C) B))
                (select (HeapContents C) B)
                defObj)))
  (and (= A (|item::next| (getitem a!1))) ((_ is O_item) a!1)))
      )
      (inv_main544_9 C B A)
    )
  )
)
(assert
  (forall ( (A Heap) (B Int) (C Int) (D Int) (E Heap) ) 
    (=>
      (and
        (inv_main530_5 E D C B)
        (let ((a!1 (ite (and (not (<= B 0)) (>= (HeapSize E) B))
                (select (HeapContents E) B)
                defObj)))
(let ((a!2 (O_item (item D (|item::data| (getitem a!1))))))
(let ((a!3 (ite (and (not (<= B 0)) (>= (HeapSize E) B))
                (HeapCtor (HeapSize E) (store (HeapContents E) B a!2))
                E)))
  (and (= A a!3) ((_ is O_item) a!1)))))
      )
      (inv_main_3 A D C B)
    )
  )
)
(assert
  (forall ( (A Int) (B Heap) (C Int) (D Int) (E Heap) (F Int) (G Int) (H Int) (I Heap) ) 
    (=>
      (and
        (inv_main544_9 I H G)
        (let ((a!1 (ite (and (not (<= H 0)) (>= (HeapSize I) H))
                (select (HeapContents I) H)
                defObj))
      (a!5 (ite (and (not (<= D 0)) (>= (HeapSize E) D))
                (HeapCtor (HeapSize E) (store (HeapContents E) D defObj))
                E)))
(let ((a!2 (not (<= (|item::data| (getitem a!1)) 0)))
      (a!4 (HeapCtor (HeapSize I)
                     (store (HeapContents I)
                            (|item::data| (getitem a!1))
                            defObj))))
(let ((a!3 (and a!2 (>= (HeapSize I) (|item::data| (getitem a!1))))))
  (and (not (= F 0))
       (= F C)
       (= D H)
       (= C G)
       (= A D)
       (= E (ite a!3 a!4 I))
       (= B a!5)
       ((_ is O_item) a!1)))))
      )
      (inv_main_10 B F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Heap) (E Heap) (F Int) (G Int) (H Int) (I Heap) ) 
    (=>
      (and
        (inv_main551_13 I H G)
        (let ((a!1 (ite (and (not (<= H 0)) (>= (HeapSize I) H))
                (select (HeapContents I) H)
                defObj))
      (a!5 (ite (and (not (<= C 0)) (>= (HeapSize D) C))
                (HeapCtor (HeapSize D) (store (HeapContents D) C defObj))
                D)))
(let ((a!2 (not (<= (|item::data| (getitem a!1)) 0)))
      (a!4 (HeapCtor (HeapSize I)
                     (store (HeapContents I)
                            (|item::data| (getitem a!1))
                            defObj))))
(let ((a!3 (and a!2 (>= (HeapSize I) (|item::data| (getitem a!1))))))
  (and (= B C)
       (not (= F 0))
       (= F A)
       (= C H)
       (= A G)
       (= D (ite a!3 a!4 I))
       (= E a!5)
       ((_ is O_item) a!1)))))
      )
      (inv_main_10 E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Heap) (E Heap) (F Int) (G Int) (H Heap) ) 
    (=>
      (and
        (inv_main_10 H G)
        (let ((a!1 (ite (and (not (<= G 0)) (>= (HeapSize H) G))
                (select (HeapContents H) G)
                defObj))
      (a!2 (ite (and (not (<= C 0)) (>= (HeapSize D) C))
                (HeapCtor (HeapSize D) (store (HeapContents D) C defObj))
                D)))
  (and (not (= A 0))
       (= A (|item::next| (getitem a!1)))
       (not (= F 0))
       (= F A)
       (= C G)
       (= B C)
       (= D H)
       (= E a!2)
       ((_ is O_item) a!1)))
      )
      (inv_main_10 E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Heap) ) 
    (=>
      (and
        (inv_main530_5 D C B A)
        (let ((a!1 (ite (and (not (<= A 0)) (>= (HeapSize D) A))
                (select (HeapContents D) A)
                defObj)))
  (not ((_ is O_item) a!1)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Heap) ) 
    (=>
      (and
        (inv_main_3 D C B A)
        (let ((a!1 (ite (and (not (<= A 0)) (>= (HeapSize D) A))
                (select (HeapContents D) A)
                defObj)))
  (not ((_ is O_item) a!1)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Heap) ) 
    (=>
      (and
        (inv_main_3 D C B A)
        (let ((a!1 (ite (and (not (<= A 0)) (>= (HeapSize D) A))
                (select (HeapContents D) A)
                defObj)))
(let ((a!2 (not (= (|item::next| (getitem a!1)) 0)))
      (a!3 (not (<= (|item::next| (getitem a!1)) 0))))
(let ((a!4 (and a!3 (>= (HeapSize D) (|item::next| (getitem a!1))))))
(let ((a!5 (ite a!4
                (select (HeapContents D) (|item::next| (getitem a!1)))
                defObj)))
  (and ((_ is O_item) a!1) a!2 (not ((_ is O_item) a!5)))))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Heap) ) 
    (=>
      (and
        (inv_main532_18 E D C B A)
        (let ((a!1 (ite (and (not (<= B 0)) (>= (HeapSize E) B))
                (select (HeapContents E) B)
                defObj)))
  (not ((_ is O_item) a!1)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Heap) ) 
    (=>
      (and
        (inv_main543_9 B A)
        (let ((a!1 (ite (and (not (<= A 0)) (>= (HeapSize B) A))
                (select (HeapContents B) A)
                defObj)))
  (not ((_ is O_item) a!1)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Heap) ) 
    (=>
      (and
        (inv_main544_9 C B A)
        (let ((a!1 (ite (and (not (<= B 0)) (>= (HeapSize C) B))
                (select (HeapContents C) B)
                defObj)))
  (not ((_ is O_item) a!1)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Heap) ) 
    (=>
      (and
        (inv_main_10 B A)
        (let ((a!1 (ite (and (not (<= A 0)) (>= (HeapSize B) A))
                (select (HeapContents B) A)
                defObj)))
  (not ((_ is O_item) a!1)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Heap) ) 
    (=>
      (and
        (inv_main551_13 C B A)
        (let ((a!1 (ite (and (not (<= B 0)) (>= (HeapSize C) B))
                (select (HeapContents C) B)
                defObj)))
  (not ((_ is O_item) a!1)))
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

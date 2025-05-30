(set-logic HORN)

(declare-datatypes ((|node| 0)) (((|node|  (|node::next| Int) (|node::data| Int)))))
(declare-datatypes ((|AddrRange| 0)) (((|AddrRange|  (|AddrRangeStart| Int) (|AddrRangeSize| Int)))))
(declare-datatypes ((|HeapObject| 0)) (((|O_Int|  (|getInt| Int)) (|O_UInt|  (|getUInt| Int)) (|O_Addr|  (|getAddr| Int)) (|O_AddrRange|  (|getAddrRange| AddrRange)) (|O_node|  (|getnode| node)) (|defObj| ))))
(declare-datatypes ((|Heap| 0)) (((|HeapCtor|  (|HeapSize| Int) (|HeapContents| (Array Int HeapObject))))))
(declare-datatypes ((|AllocResHeap| 0)) (((|AllocResHeap|  (|newHeap| Heap) (|newAddr| Int)))))

(declare-fun |inv_main_20| ( Heap Int Int ) Bool)
(declare-fun |_Glue9| ( Int Int Heap Int HeapObject ) Bool)
(declare-fun |_Glue30| ( Int Int Int Int Heap HeapObject ) Bool)
(declare-fun |_Glue36| ( Int Int Heap Int HeapObject ) Bool)
(declare-fun |_Glue2| ( Int Heap HeapObject ) Bool)
(declare-fun |_Glue14| ( Int Int Int Heap ) Bool)
(declare-fun |_Glue21| ( Heap Int HeapObject ) Bool)
(declare-fun |_Glue7| ( Int Heap Int Int HeapObject ) Bool)
(declare-fun |_Glue11| ( Heap Int Int HeapObject ) Bool)
(declare-fun |inv_main600_3| ( Heap Int Int Int ) Bool)
(declare-fun |_Glue27| ( Int Int Int Heap HeapObject ) Bool)
(declare-fun |_Glue19| ( Int Heap HeapObject ) Bool)
(declare-fun |_Glue13| ( Int Heap Int Int HeapObject ) Bool)
(declare-fun |CHC_COMP_FALSE| ( ) Bool)
(declare-fun |inv_main581_3| ( Heap Int Int Int ) Bool)
(declare-fun |_Glue32| ( Heap Int Int Int HeapObject ) Bool)
(declare-fun |Inv_Heap| ( Int HeapObject ) Bool)

(assert
  (forall ( (A Int) (B AllocResHeap) (C Heap) (D HeapObject) (E node) ) 
    (=>
      (and
        (let ((a!1 (HeapCtor (+ 1 (HeapSize C))
                     (store (HeapContents C) (+ 1 (HeapSize C)) D))))
(let ((a!2 (= (AllocResHeap a!1 (+ 1 (HeapSize C))) B)))
  (and (= A (newAddr B))
       a!2
       (= (O_node E) D)
       (= (HeapCtor 0 ((as const (Array Int HeapObject)) defObj)) C))))
      )
      (Inv_Heap A D)
    )
  )
)
(assert
  (forall ( (A Heap) (B HeapObject) (C node) (D AllocResHeap) (E Heap) (F Int) (G HeapObject) (H Int) ) 
    (=>
      (and
        (Inv_Heap H G)
        (let ((a!1 (HeapCtor (+ 1 (HeapSize A))
                     (store (HeapContents A) (+ 1 (HeapSize A)) B)))
      (a!3 (ite (and (not (<= H 0)) (>= (HeapSize E) H))
                (select (HeapContents E) H)
                defObj)))
(let ((a!2 (= (AllocResHeap a!1 (+ 1 (HeapSize A))) D)))
  (and (= 0 F)
       (not (= F H))
       a!2
       (= (AllocResHeap E H) D)
       (= a!3 G)
       (= (O_node C) B)
       (>= (HeapSize E) H)
       (not (<= H 0))
       (= (HeapCtor 0 ((as const (Array Int HeapObject)) defObj)) A))))
      )
      (_Glue19 H E G)
    )
  )
)
(assert
  (forall ( (A Heap) (B HeapObject) (C node) (D AllocResHeap) (E HeapObject) (F Heap) (G Int) (H Int) ) 
    (=>
      (and
        (let ((a!1 (HeapCtor (+ 1 (HeapSize A))
                     (store (HeapContents A) (+ 1 (HeapSize A)) B)))
      (a!3 (ite (and (not (<= G 0)) (>= (HeapSize F) G))
                (select (HeapContents F) G)
                defObj))
      (a!4 (or (<= G 0) (not (>= (HeapSize F) G)))))
(let ((a!2 (= (AllocResHeap a!1 (+ 1 (HeapSize A))) D)))
  (and (= 0 H)
       (not (= H G))
       a!2
       (= (AllocResHeap F G) D)
       (= a!3 E)
       (= (O_node C) B)
       a!4
       (= (HeapCtor 0 ((as const (Array Int HeapObject)) defObj)) A))))
      )
      (_Glue19 G F E)
    )
  )
)
(assert
  (forall ( (A HeapObject) (B node) (C Int) (D node) (E HeapObject) (F Heap) (G Int) ) 
    (=>
      (and
        (_Glue19 G F E)
        (and (= (node G C) B)
     (= (getnode E) D)
     (= (|node::data| D) C)
     (= (O_node B) A)
     (>= (HeapSize F) G)
     (not (<= G 0))
     ((_ is O_node) E))
      )
      (Inv_Heap G A)
    )
  )
)
(assert
  (forall ( (A HeapObject) (B node) (C Int) (D node) (E Heap) (F HeapObject) (G Heap) (H HeapObject) (I Int) ) 
    (=>
      (and
        (_Glue19 I G F)
        (Inv_Heap I H)
        (let ((a!1 (ite (and (not (<= I 0)) (>= (HeapSize G) I))
                (HeapCtor (HeapSize G) (store (HeapContents G) I A))
                G))
      (a!2 (ite (and (not (<= I 0)) (>= (HeapSize E) I))
                (select (HeapContents E) I)
                defObj)))
  (and (= (node I C) B)
       (= (getnode F) D)
       (= a!1 E)
       (= (|node::data| D) C)
       (= a!2 H)
       (= (O_node B) A)
       (>= (HeapSize E) I)
       (not (<= I 0))
       ((_ is O_node) F)))
      )
      (_Glue21 E I H)
    )
  )
)
(assert
  (forall ( (A HeapObject) (B node) (C Int) (D node) (E HeapObject) (F Heap) (G HeapObject) (H Heap) (I Int) ) 
    (=>
      (and
        (_Glue19 I H G)
        (let ((a!1 (ite (and (not (<= I 0)) (>= (HeapSize H) I))
                (HeapCtor (HeapSize H) (store (HeapContents H) I A))
                H))
      (a!2 (ite (and (not (<= I 0)) (>= (HeapSize F) I))
                (select (HeapContents F) I)
                defObj))
      (a!3 (or (<= I 0) (not (>= (HeapSize F) I)))))
  (and (= (node I C) B)
       (= (getnode G) D)
       (= a!1 F)
       (= (|node::data| D) C)
       (= a!2 E)
       (= (O_node B) A)
       a!3
       ((_ is O_node) G)))
      )
      (_Glue21 F I E)
    )
  )
)
(assert
  (forall ( (A HeapObject) (B node) (C Int) (D node) (E HeapObject) (F Int) (G Heap) ) 
    (=>
      (and
        (_Glue21 G F E)
        (and (= (node C 1) B)
     (= (getnode E) D)
     (= (|node::next| D) C)
     (= (O_node B) A)
     (>= (HeapSize G) F)
     (not (<= F 0))
     ((_ is O_node) E))
      )
      (Inv_Heap F A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Heap) (D HeapObject) (E node) (F Int) (G node) (H HeapObject) (I Int) (J Heap) ) 
    (=>
      (and
        (_Glue21 J I H)
        (let ((a!1 (ite (and (not (<= I 0)) (>= (HeapSize J) I))
                (HeapCtor (HeapSize J) (store (HeapContents J) I D))
                J)))
  (and (= (node F 1) E)
       (= (getnode H) G)
       (= a!1 C)
       (= (|node::next| G) F)
       (= B I)
       (= A 5)
       (= (O_node E) D)
       ((_ is O_node) H)))
      )
      (inv_main581_3 C A I B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Heap) (E HeapObject) (F Int) ) 
    (=>
      (and
        (inv_main_20 D A F)
        (Inv_Heap F E)
        (let ((a!1 (ite (and (not (<= F 0)) (>= (HeapSize D) F))
                (select (HeapContents D) F)
                defObj)))
  (and (= A (+ (- 1) C)) (= a!1 E) (>= (HeapSize D) F) (not (<= F 0)) (= 0 B)))
      )
      (_Glue36 B C D F E)
    )
  )
)
(assert
  (forall ( (A Int) (B HeapObject) (C Int) (D Int) (E Int) (F Heap) ) 
    (=>
      (and
        (inv_main_20 F A D)
        (let ((a!1 (ite (and (not (<= D 0)) (>= (HeapSize F) D))
                (select (HeapContents F) D)
                defObj))
      (a!2 (or (<= D 0) (not (>= (HeapSize F) D)))))
  (and (= A (+ (- 1) E)) (= a!1 B) a!2 (= 0 C)))
      )
      (_Glue36 C E F D B)
    )
  )
)
(assert
  (forall ( (A HeapObject) (B Int) (C node) (D HeapObject) (E Int) (F Heap) (G Int) (H Int) ) 
    (=>
      (and
        (_Glue36 H G F E D)
        (and (= (getnode D) C)
     (= (|node::data| C) (+ (- 1) G))
     (= (|node::next| C) B)
     (not (= B H))
     (= defObj A)
     (>= (HeapSize F) E)
     (not (<= E 0))
     ((_ is O_node) D))
      )
      (Inv_Heap E A)
    )
  )
)
(assert
  (forall ( (A Heap) (B HeapObject) (C Int) (D node) (E HeapObject) (F Int) (G Heap) (H Int) (I Int) ) 
    (=>
      (and
        (_Glue36 I H G F E)
        (let ((a!1 (ite (and (not (<= F 0)) (>= (HeapSize G) F))
                (HeapCtor (HeapSize G) (store (HeapContents G) F B))
                G)))
  (and (= (getnode E) D)
       (= a!1 A)
       (= (|node::data| D) (+ (- 1) H))
       (= (|node::next| D) C)
       (not (= C I))
       (= defObj B)
       ((_ is O_node) E)))
      )
      (inv_main_20 A H C)
    )
  )
)
(assert
  (forall ( (A Int) (B AllocResHeap) (C HeapObject) (D node) (E Int) (F Int) (G Int) (H Heap) ) 
    (=>
      (and
        (inv_main581_3 H G F E)
        (let ((a!1 (HeapCtor (+ 1 (HeapSize H))
                     (store (HeapContents H) (+ 1 (HeapSize H)) C))))
(let ((a!2 (= (AllocResHeap a!1 (+ 1 (HeapSize H))) B)))
  (and a!2 (= (O_node D) C) (= A (newAddr B)))))
      )
      (Inv_Heap A C)
    )
  )
)
(assert
  (forall ( (A AllocResHeap) (B HeapObject) (C node) (D Heap) (E Int) (F Int) (G Int) (H Int) (I Heap) (J HeapObject) (K Int) ) 
    (=>
      (and
        (inv_main581_3 I H G F)
        (Inv_Heap K J)
        (let ((a!1 (HeapCtor (+ 1 (HeapSize I))
                     (store (HeapContents I) (+ 1 (HeapSize I)) B)))
      (a!3 (ite (and (not (<= K 0)) (>= (HeapSize D) K))
                (select (HeapContents D) K)
                defObj)))
(let ((a!2 (= (AllocResHeap a!1 (+ 1 (HeapSize I))) A)))
  (and (not (= E K))
       a!2
       (= (AllocResHeap D K) A)
       (= a!3 J)
       (= (O_node C) B)
       (>= (HeapSize D) K)
       (not (<= K 0))
       (= 0 E))))
      )
      (_Glue27 F H K D J)
    )
  )
)
(assert
  (forall ( (A AllocResHeap) (B HeapObject) (C node) (D HeapObject) (E Heap) (F Int) (G Int) (H Int) (I Int) (J Int) (K Heap) ) 
    (=>
      (and
        (inv_main581_3 K J I H)
        (let ((a!1 (HeapCtor (+ 1 (HeapSize K))
                     (store (HeapContents K) (+ 1 (HeapSize K)) B)))
      (a!3 (ite (and (not (<= F 0)) (>= (HeapSize E) F))
                (select (HeapContents E) F)
                defObj))
      (a!4 (or (<= F 0) (not (>= (HeapSize E) F)))))
(let ((a!2 (= (AllocResHeap a!1 (+ 1 (HeapSize K))) A)))
  (and (not (= G F))
       a!2
       (= (AllocResHeap E F) A)
       (= a!3 D)
       (= (O_node C) B)
       a!4
       (= 0 G))))
      )
      (_Glue27 H J F E D)
    )
  )
)
(assert
  (forall ( (A HeapObject) (B node) (C Int) (D node) (E HeapObject) (F Heap) (G Int) (H Int) (I Int) ) 
    (=>
      (and
        (_Glue27 I H G F E)
        (and (= (node I C) B)
     (= (getnode E) D)
     (= (|node::data| D) C)
     (= (O_node B) A)
     (>= (HeapSize F) G)
     (not (<= G 0))
     ((_ is O_node) E))
      )
      (Inv_Heap G A)
    )
  )
)
(assert
  (forall ( (A Int) (B AllocResHeap) (C Heap) (D HeapObject) (E node) ) 
    (=>
      (and
        (let ((a!1 (HeapCtor (+ 1 (HeapSize C))
                     (store (HeapContents C) (+ 1 (HeapSize C)) D))))
(let ((a!2 (= (AllocResHeap a!1 (+ 1 (HeapSize C))) B)))
  (and (= A (newAddr B))
       a!2
       (= (O_node E) D)
       (= (HeapCtor 0 ((as const (Array Int HeapObject)) defObj)) C))))
      )
      (Inv_Heap A D)
    )
  )
)
(assert
  (forall ( (A Heap) (B HeapObject) (C node) (D AllocResHeap) (E Heap) (F Int) (G HeapObject) (H Int) ) 
    (=>
      (and
        (Inv_Heap H G)
        (let ((a!1 (HeapCtor (+ 1 (HeapSize A))
                     (store (HeapContents A) (+ 1 (HeapSize A)) B)))
      (a!3 (ite (and (not (<= H 0)) (>= (HeapSize E) H))
                (select (HeapContents E) H)
                defObj)))
(let ((a!2 (= (AllocResHeap a!1 (+ 1 (HeapSize A))) D)))
  (and (= 0 F)
       (not (= F H))
       a!2
       (= (AllocResHeap E H) D)
       (= a!3 G)
       (= (O_node C) B)
       (>= (HeapSize E) H)
       (not (<= H 0))
       (= (HeapCtor 0 ((as const (Array Int HeapObject)) defObj)) A))))
      )
      (_Glue2 H E G)
    )
  )
)
(assert
  (forall ( (A Heap) (B HeapObject) (C node) (D AllocResHeap) (E HeapObject) (F Heap) (G Int) (H Int) ) 
    (=>
      (and
        (let ((a!1 (HeapCtor (+ 1 (HeapSize A))
                     (store (HeapContents A) (+ 1 (HeapSize A)) B)))
      (a!3 (ite (and (not (<= G 0)) (>= (HeapSize F) G))
                (select (HeapContents F) G)
                defObj))
      (a!4 (or (<= G 0) (not (>= (HeapSize F) G)))))
(let ((a!2 (= (AllocResHeap a!1 (+ 1 (HeapSize A))) D)))
  (and (= 0 H)
       (not (= H G))
       a!2
       (= (AllocResHeap F G) D)
       (= a!3 E)
       (= (O_node C) B)
       a!4
       (= (HeapCtor 0 ((as const (Array Int HeapObject)) defObj)) A))))
      )
      (_Glue2 G F E)
    )
  )
)
(assert
  (forall ( (A HeapObject) (B node) (C Int) (D node) (E HeapObject) (F Heap) (G Int) ) 
    (=>
      (and
        (_Glue2 G F E)
        (and (= (node G C) B)
     (= (getnode E) D)
     (= (|node::data| D) C)
     (= (O_node B) A)
     (>= (HeapSize F) G)
     (not (<= G 0))
     ((_ is O_node) E))
      )
      (Inv_Heap G A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C AllocResHeap) (D HeapObject) (E node) (F Int) (G Int) (H Int) (I Heap) ) 
    (=>
      (and
        (inv_main581_3 I A G F)
        (let ((a!1 (HeapCtor (+ 1 (HeapSize I))
                     (store (HeapContents I) (+ 1 (HeapSize I)) D))))
(let ((a!2 (= (AllocResHeap a!1 (+ 1 (HeapSize I))) C)))
  (and (= A (+ 1 H)) a!2 (= (O_node E) D) (= B (newAddr C)))))
      )
      (Inv_Heap B D)
    )
  )
)
(assert
  (forall ( (A Int) (B AllocResHeap) (C HeapObject) (D node) (E Heap) (F Int) (G Int) (H Int) (I Int) (J Heap) (K HeapObject) (L Int) ) 
    (=>
      (and
        (inv_main581_3 J A H G)
        (Inv_Heap L K)
        (let ((a!1 (HeapCtor (+ 1 (HeapSize J))
                     (store (HeapContents J) (+ 1 (HeapSize J)) C)))
      (a!3 (ite (and (not (<= L 0)) (>= (HeapSize E) L))
                (select (HeapContents E) L)
                defObj)))
(let ((a!2 (= (AllocResHeap a!1 (+ 1 (HeapSize J))) B)))
  (and (= A (+ 1 I))
       (not (= F L))
       a!2
       (= (AllocResHeap E L) B)
       (= a!3 K)
       (= (O_node D) C)
       (>= (HeapSize E) L)
       (not (<= L 0))
       (= 0 F))))
      )
      (_Glue30 G I H L E K)
    )
  )
)
(assert
  (forall ( (A Int) (B AllocResHeap) (C HeapObject) (D node) (E HeapObject) (F Heap) (G Int) (H Int) (I Int) (J Int) (K Int) (L Heap) ) 
    (=>
      (and
        (inv_main581_3 L A J I)
        (let ((a!1 (HeapCtor (+ 1 (HeapSize L))
                     (store (HeapContents L) (+ 1 (HeapSize L)) C)))
      (a!3 (ite (and (not (<= G 0)) (>= (HeapSize F) G))
                (select (HeapContents F) G)
                defObj))
      (a!4 (or (<= G 0) (not (>= (HeapSize F) G)))))
(let ((a!2 (= (AllocResHeap a!1 (+ 1 (HeapSize L))) B)))
  (and (= A (+ 1 K))
       (not (= H G))
       a!2
       (= (AllocResHeap F G) B)
       (= a!3 E)
       (= (O_node D) C)
       a!4
       (= 0 H))))
      )
      (_Glue30 I K J G F E)
    )
  )
)
(assert
  (forall ( (A HeapObject) (B node) (C Int) (D node) (E HeapObject) (F Heap) (G Int) (H Int) (I Int) (J Int) ) 
    (=>
      (and
        (_Glue30 J I H G F E)
        (and (= (node J C) B)
     (= (getnode E) D)
     (= (|node::data| D) C)
     (= (O_node B) A)
     (>= (HeapSize F) G)
     (not (<= G 0))
     ((_ is O_node) E))
      )
      (Inv_Heap G A)
    )
  )
)
(assert
  (forall ( (A HeapObject) (B node) (C Int) (D node) (E Heap) (F HeapObject) (G Heap) (H Int) (I Int) (J Int) (K HeapObject) (L Int) ) 
    (=>
      (and
        (_Glue30 J I H L G F)
        (Inv_Heap L K)
        (let ((a!1 (ite (and (not (<= L 0)) (>= (HeapSize G) L))
                (HeapCtor (HeapSize G) (store (HeapContents G) L A))
                G))
      (a!2 (ite (and (not (<= L 0)) (>= (HeapSize E) L))
                (select (HeapContents E) L)
                defObj)))
  (and (= (node J C) B)
       (= (getnode F) D)
       (= a!1 E)
       (= (|node::data| D) C)
       (= a!2 K)
       (= (O_node B) A)
       (>= (HeapSize E) L)
       (not (<= L 0))
       ((_ is O_node) F)))
      )
      (_Glue32 E I H L K)
    )
  )
)
(assert
  (forall ( (A HeapObject) (B node) (C Int) (D node) (E HeapObject) (F Heap) (G HeapObject) (H Heap) (I Int) (J Int) (K Int) (L Int) ) 
    (=>
      (and
        (_Glue30 L K J I H G)
        (let ((a!1 (ite (and (not (<= I 0)) (>= (HeapSize H) I))
                (HeapCtor (HeapSize H) (store (HeapContents H) I A))
                H))
      (a!2 (ite (and (not (<= I 0)) (>= (HeapSize F) I))
                (select (HeapContents F) I)
                defObj))
      (a!3 (or (<= I 0) (not (>= (HeapSize F) I)))))
  (and (= (node L C) B)
       (= (getnode G) D)
       (= a!1 F)
       (= (|node::data| D) C)
       (= a!2 E)
       (= (O_node B) A)
       a!3
       ((_ is O_node) G)))
      )
      (_Glue32 F K J I E)
    )
  )
)
(assert
  (forall ( (A HeapObject) (B node) (C Int) (D node) (E HeapObject) (F Int) (G Int) (H Int) (I Heap) ) 
    (=>
      (and
        (_Glue32 I H G F E)
        (and (= (node C 1) B)
     (= (getnode E) D)
     (= (|node::next| D) C)
     (= (O_node B) A)
     (>= (HeapSize I) F)
     (<= 1 H)
     (not (<= F 0))
     ((_ is O_node) E))
      )
      (Inv_Heap F A)
    )
  )
)
(assert
  (forall ( (A Heap) (B HeapObject) (C node) (D Int) (E node) (F HeapObject) (G Int) (H Int) (I Int) (J Heap) ) 
    (=>
      (and
        (_Glue32 J I H G F)
        (let ((a!1 (ite (and (not (<= G 0)) (>= (HeapSize J) G))
                (HeapCtor (HeapSize J) (store (HeapContents J) G B))
                J)))
  (and (= (node D 1) C)
       (= (getnode F) E)
       (= a!1 A)
       (= (|node::next| E) D)
       (= (O_node C) B)
       (<= 1 I)
       ((_ is O_node) F)))
      )
      (inv_main581_3 A I H G)
    )
  )
)
(assert
  (forall ( (A Int) (B AllocResHeap) (C Heap) (D HeapObject) (E node) ) 
    (=>
      (and
        (let ((a!1 (HeapCtor (+ 1 (HeapSize C))
                     (store (HeapContents C) (+ 1 (HeapSize C)) D))))
(let ((a!2 (= (AllocResHeap a!1 (+ 1 (HeapSize C))) B)))
  (and (= A (newAddr B))
       a!2
       (= (O_node E) D)
       (= (HeapCtor 0 ((as const (Array Int HeapObject)) defObj)) C))))
      )
      (Inv_Heap A D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Heap) (D HeapObject) (E Int) ) 
    (=>
      (and
        (Inv_Heap E D)
        (inv_main581_3 C B E A)
        (let ((a!1 (ite (and (not (<= E 0)) (>= (HeapSize C) E))
                (select (HeapContents C) E)
                defObj)))
  (and (>= (HeapSize C) E) (not (<= E 0)) (= a!1 D)))
      )
      (_Glue9 A B C E D)
    )
  )
)
(assert
  (forall ( (A HeapObject) (B Int) (C Int) (D Int) (E Heap) ) 
    (=>
      (and
        (inv_main581_3 E D C B)
        (let ((a!1 (or (<= C 0) (not (>= (HeapSize E) C))))
      (a!2 (ite (and (not (<= C 0)) (>= (HeapSize E) C))
                (select (HeapContents E) C)
                defObj)))
  (and a!1 (= a!2 A)))
      )
      (_Glue9 B D E C A)
    )
  )
)
(assert
  (forall ( (A HeapObject) (B node) (C Int) (D node) (E HeapObject) (F Int) (G Heap) (H Int) (I Int) ) 
    (=>
      (and
        (_Glue9 I H G F E)
        (and (= (node I C) B)
     (= (getnode E) D)
     (= (|node::data| D) C)
     (= (O_node B) A)
     (>= (HeapSize G) F)
     (not (<= 2 H))
     (not (<= F 0))
     ((_ is O_node) E))
      )
      (Inv_Heap F A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Heap) (D HeapObject) (E node) (F Int) (G node) (H HeapObject) (I Int) (J Heap) (K Int) (L Int) ) 
    (=>
      (and
        (_Glue9 L K J I H)
        (let ((a!1 (ite (and (not (<= I 0)) (>= (HeapSize J) I))
                (HeapCtor (HeapSize J) (store (HeapContents J) I D))
                J)))
  (and (= (node L F) E)
       (= (getnode H) G)
       (= a!1 C)
       (= (|node::data| G) F)
       (= B L)
       (= A 1)
       (= (O_node E) D)
       (not (<= 2 K))
       ((_ is O_node) H)))
      )
      (inv_main600_3 C L A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Heap) (E HeapObject) (F Int) ) 
    (=>
      (and
        (Inv_Heap F E)
        (inv_main600_3 D C A F)
        (let ((a!1 (ite (and (not (<= F 0)) (>= (HeapSize D) F))
                (select (HeapContents D) F)
                defObj)))
  (and (= a!1 E) (>= (HeapSize D) F) (not (<= F 0)) (= A (+ (- 1) B))))
      )
      (_Glue7 C D B F E)
    )
  )
)
(assert
  (forall ( (A Int) (B HeapObject) (C Int) (D Int) (E Int) (F Heap) ) 
    (=>
      (and
        (inv_main600_3 F E A C)
        (let ((a!1 (ite (and (not (<= C 0)) (>= (HeapSize F) C))
                (select (HeapContents F) C)
                defObj))
      (a!2 (or (<= C 0) (not (>= (HeapSize F) C)))))
  (and (= a!1 B) a!2 (= A (+ (- 1) D))))
      )
      (_Glue7 E F D C B)
    )
  )
)
(assert
  (forall ( (A HeapObject) (B node) (C Int) (D node) (E HeapObject) (F Int) (G Int) (H Heap) (I Int) ) 
    (=>
      (and
        (_Glue7 I H G F E)
        (and (= (node C (+ (- 1) G)) B)
     (= (getnode E) D)
     (= (|node::data| D) 1)
     (= (|node::next| D) C)
     (= (O_node B) A)
     (>= (HeapSize H) F)
     (not (<= F 0))
     ((_ is O_node) E))
      )
      (Inv_Heap F A)
    )
  )
)
(assert
  (forall ( (A HeapObject) (B node) (C Int) (D node) (E Int) (F node) (G Heap) (H HeapObject) (I Int) (J Heap) (K Int) (L HeapObject) (M Int) ) 
    (=>
      (and
        (_Glue7 K J I M H)
        (Inv_Heap M L)
        (let ((a!1 (ite (and (not (<= M 0)) (>= (HeapSize J) M))
                (HeapCtor (HeapSize J) (store (HeapContents J) M A))
                J))
      (a!2 (ite (and (not (<= M 0)) (>= (HeapSize G) M))
                (select (HeapContents G) M)
                defObj)))
  (and ((_ is O_node) L)
       (= (node C (+ (- 1) I)) B)
       (= (getnode H) D)
       (= (getnode L) F)
       (= a!1 G)
       (= (|node::data| D) 1)
       (= (|node::next| D) C)
       (= (|node::next| F) E)
       (not (= E K))
       (= a!2 L)
       (= (O_node B) A)
       (>= (HeapSize G) M)
       (not (<= M 0))
       ((_ is O_node) H)))
      )
      (inv_main600_3 G K I E)
    )
  )
)
(assert
  (forall ( (A HeapObject) (B node) (C Int) (D node) (E Int) (F node) (G HeapObject) (H Heap) (I HeapObject) (J Int) (K Int) (L Heap) (M Int) ) 
    (=>
      (and
        (_Glue7 M L K J I)
        (let ((a!1 (ite (and (not (<= J 0)) (>= (HeapSize L) J))
                (HeapCtor (HeapSize L) (store (HeapContents L) J A))
                L))
      (a!2 (ite (and (not (<= J 0)) (>= (HeapSize H) J))
                (select (HeapContents H) J)
                defObj))
      (a!3 (or (<= J 0) (not (>= (HeapSize H) J)))))
  (and ((_ is O_node) G)
       (= (node C (+ (- 1) K)) B)
       (= (getnode I) D)
       (= (getnode G) F)
       (= a!1 H)
       (= (|node::data| D) 1)
       (= (|node::next| D) C)
       (= (|node::next| F) E)
       (not (= E M))
       (= a!2 G)
       (= (O_node B) A)
       a!3
       ((_ is O_node) I)))
      )
      (inv_main600_3 H M K E)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Heap) (F HeapObject) (G Int) ) 
    (=>
      (and
        (Inv_Heap G F)
        (inv_main600_3 E D A G)
        (let ((a!1 (ite (and (not (<= G 0)) (>= (HeapSize E) G))
                (select (HeapContents E) G)
                defObj)))
  (and (= a!1 F) (>= (HeapSize E) G) (not (<= G 0)) (= A (+ 4 C))))
      )
      (_Glue13 B E C G F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C HeapObject) (D Int) (E Int) (F Int) (G Heap) ) 
    (=>
      (and
        (inv_main600_3 G F A D)
        (let ((a!1 (ite (and (not (<= D 0)) (>= (HeapSize G) D))
                (select (HeapContents G) D)
                defObj))
      (a!2 (or (<= D 0) (not (>= (HeapSize G) D)))))
  (and (= a!1 C) a!2 (= A (+ 4 E))))
      )
      (_Glue13 B G E D C)
    )
  )
)
(assert
  (forall ( (A Int) (B HeapObject) (C node) (D Int) (E node) (F Int) (G HeapObject) (H Int) (I Int) (J Heap) (K Int) ) 
    (=>
      (and
        (inv_main600_3 J F A H)
        (_Glue13 K J I H G)
        (and (= (node D (+ 4 I)) C)
     (= (getnode G) E)
     (= (|node::data| E) 1)
     (= (|node::next| E) D)
     (= A (+ 4 I))
     (= (O_node C) B)
     (>= (HeapSize J) H)
     (not (<= H 0))
     ((_ is O_node) G))
      )
      (Inv_Heap H B)
    )
  )
)
(assert
  (forall ( (A Int) (B Heap) (C HeapObject) (D node) (E Int) (F node) (G Int) (H HeapObject) (I Int) (J Int) (K Heap) (L Int) ) 
    (=>
      (and
        (inv_main600_3 K G A I)
        (_Glue13 L K J I H)
        (let ((a!1 (ite (and (not (<= I 0)) (>= (HeapSize K) I))
                (HeapCtor (HeapSize K) (store (HeapContents K) I C))
                K)))
  (and (= (node E (+ 4 J)) D)
       (= (getnode H) F)
       (= a!1 B)
       (= (|node::data| F) 1)
       (= (|node::next| F) E)
       (= A (+ 4 J))
       (= (O_node D) C)
       ((_ is O_node) H)))
      )
      (_Glue14 I J L B)
    )
  )
)
(assert
  (forall ( (A Int) (B node) (C Heap) (D Heap) (E Int) (F Int) (G HeapObject) (H Int) ) 
    (=>
      (and
        (inv_main600_3 C E A H)
        (_Glue14 H F E D)
        (Inv_Heap H G)
        (let ((a!1 (ite (and (not (<= H 0)) (>= (HeapSize D) H))
                (select (HeapContents D) H)
                defObj)))
  (and (= (getnode G) B)
       (= (|node::next| B) E)
       (= A (+ 4 F))
       (= a!1 G)
       (>= (HeapSize D) H)
       (not (<= H 0))
       ((_ is O_node) G)))
      )
      (inv_main_20 D F E)
    )
  )
)
(assert
  (forall ( (A Int) (B node) (C HeapObject) (D Heap) (E Heap) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (inv_main600_3 D F A H)
        (_Glue14 H G F E)
        (let ((a!1 (ite (and (not (<= H 0)) (>= (HeapSize E) H))
                (select (HeapContents E) H)
                defObj))
      (a!2 (or (<= H 0) (not (>= (HeapSize E) H)))))
  (and (= (getnode C) B)
       (= (|node::next| B) F)
       (= A (+ 4 G))
       (= a!1 C)
       a!2
       ((_ is O_node) C)))
      )
      (inv_main_20 E G F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Heap) (D HeapObject) (E Int) ) 
    (=>
      (and
        (Inv_Heap E D)
        (inv_main600_3 C B A E)
        (let ((a!1 (ite (and (not (<= E 0)) (>= (HeapSize C) E))
                (select (HeapContents C) E)
                defObj)))
  (and (>= (HeapSize C) E) (not (<= E 0)) (= a!1 D)))
      )
      (_Glue11 C A E D)
    )
  )
)
(assert
  (forall ( (A HeapObject) (B Int) (C Int) (D Int) (E Heap) ) 
    (=>
      (and
        (inv_main600_3 E D C B)
        (let ((a!1 (or (<= B 0) (not (>= (HeapSize E) B))))
      (a!2 (ite (and (not (<= B 0)) (>= (HeapSize E) B))
                (select (HeapContents E) B)
                defObj)))
  (and a!1 (= a!2 A)))
      )
      (_Glue11 E C B A)
    )
  )
)
(assert
  (forall ( (A HeapObject) (B node) (C Int) (D node) (E HeapObject) (F Int) (G Int) (H Heap) ) 
    (=>
      (and
        (_Glue11 H G F E)
        (and (= (node C G) B)
     (= (getnode E) D)
     (= (|node::data| D) 1)
     (= (|node::next| D) C)
     (= (O_node B) A)
     (>= (HeapSize H) F)
     (not (<= F 0))
     ((_ is O_node) E))
      )
      (Inv_Heap F A)
    )
  )
)
(assert
  (forall ( (A Int) (B AllocResHeap) (C HeapObject) (D node) (E Int) (F Int) (G Int) (H Heap) ) 
    (=>
      (and
        (inv_main581_3 H G F E)
        (let ((a!1 (HeapCtor (+ 1 (HeapSize H))
                     (store (HeapContents H) (+ 1 (HeapSize H)) C))))
(let ((a!2 (= (AllocResHeap a!1 (+ 1 (HeapSize H))) B)))
  (and a!2 (= (O_node D) C) (= A (newAddr B)))))
      )
      (Inv_Heap A C)
    )
  )
)
(assert
  (forall ( (A Int) (B Heap) (C HeapObject) (D Int) ) 
    (=>
      (and
        (inv_main_20 B A D)
        (Inv_Heap D C)
        (let ((a!1 (ite (and (not (<= D 0)) (>= (HeapSize B) D))
                (select (HeapContents B) D)
                defObj)))
  (and (= a!1 C) (>= (HeapSize B) D) (not (<= D 0)) (not ((_ is O_node) C))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A HeapObject) (B Int) (C Int) (D Heap) ) 
    (=>
      (and
        (inv_main_20 D C B)
        (let ((a!1 (ite (and (not (<= B 0)) (>= (HeapSize D) B))
                (select (HeapContents D) B)
                defObj))
      (a!2 (or (<= B 0) (not (>= (HeapSize D) B)))))
  (and (= a!1 A) a!2 (not ((_ is O_node) A))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A HeapObject) (B node) (C Int) (D node) (E Heap) (F HeapObject) (G Heap) (H Int) (I Int) (J HeapObject) (K Int) ) 
    (=>
      (and
        (_Glue27 I H K G F)
        (Inv_Heap K J)
        (let ((a!1 (ite (and (not (<= K 0)) (>= (HeapSize G) K))
                (HeapCtor (HeapSize G) (store (HeapContents G) K A))
                G))
      (a!2 (ite (and (not (<= K 0)) (>= (HeapSize E) K))
                (select (HeapContents E) K)
                defObj)))
  (and (not ((_ is O_node) J))
       (= (node I C) B)
       (= (getnode F) D)
       (= a!1 E)
       (= (|node::data| D) C)
       (= a!2 J)
       (= (O_node B) A)
       (>= (HeapSize E) K)
       (<= 2 H)
       (not (<= K 0))
       ((_ is O_node) F)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A HeapObject) (B node) (C Int) (D node) (E HeapObject) (F Heap) (G HeapObject) (H Heap) (I Int) (J Int) (K Int) ) 
    (=>
      (and
        (_Glue27 K J I H G)
        (let ((a!1 (ite (and (not (<= I 0)) (>= (HeapSize H) I))
                (HeapCtor (HeapSize H) (store (HeapContents H) I A))
                H))
      (a!2 (ite (and (not (<= I 0)) (>= (HeapSize F) I))
                (select (HeapContents F) I)
                defObj))
      (a!3 (or (<= I 0) (not (>= (HeapSize F) I)))))
  (and (not ((_ is O_node) E))
       (= (node K C) B)
       (= (getnode G) D)
       (= a!1 F)
       (= (|node::data| D) C)
       (= a!2 E)
       (= (O_node B) A)
       (<= 2 J)
       a!3
       ((_ is O_node) G)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A HeapObject) (B node) (C Int) (D node) (E Heap) (F HeapObject) (G Heap) (H HeapObject) (I Int) ) 
    (=>
      (and
        (_Glue2 I G F)
        (Inv_Heap I H)
        (let ((a!1 (ite (and (not (<= I 0)) (>= (HeapSize G) I))
                (HeapCtor (HeapSize G) (store (HeapContents G) I A))
                G))
      (a!2 (ite (and (not (<= I 0)) (>= (HeapSize E) I))
                (select (HeapContents E) I)
                defObj)))
  (and (not ((_ is O_node) H))
       (= (node I C) B)
       (= (getnode F) D)
       (= a!1 E)
       (= (|node::data| D) C)
       (= a!2 H)
       (= (O_node B) A)
       (>= (HeapSize E) I)
       (not (<= I 0))
       ((_ is O_node) F)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A HeapObject) (B node) (C Int) (D node) (E HeapObject) (F Heap) (G HeapObject) (H Heap) (I Int) ) 
    (=>
      (and
        (_Glue2 I H G)
        (let ((a!1 (ite (and (not (<= I 0)) (>= (HeapSize H) I))
                (HeapCtor (HeapSize H) (store (HeapContents H) I A))
                H))
      (a!2 (ite (and (not (<= I 0)) (>= (HeapSize F) I))
                (select (HeapContents F) I)
                defObj))
      (a!3 (or (<= I 0) (not (>= (HeapSize F) I)))))
  (and ((_ is O_node) G)
       (= (node I C) B)
       (= (getnode G) D)
       (= a!1 F)
       (= (|node::data| D) C)
       (= a!2 E)
       (= (O_node B) A)
       a!3
       (not ((_ is O_node) E))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Heap) (D HeapObject) (E Int) ) 
    (=>
      (and
        (inv_main581_3 C B E A)
        (Inv_Heap E D)
        (let ((a!1 (ite (and (not (<= E 0)) (>= (HeapSize C) E))
                (select (HeapContents C) E)
                defObj)))
  (and (= a!1 D)
       (>= (HeapSize C) E)
       (not (<= 2 B))
       (not (<= E 0))
       (not ((_ is O_node) D))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A HeapObject) (B Int) (C Int) (D Int) (E Heap) ) 
    (=>
      (and
        (inv_main581_3 E D C B)
        (let ((a!1 (ite (and (not (<= C 0)) (>= (HeapSize E) C))
                (select (HeapContents E) C)
                defObj))
      (a!2 (or (<= C 0) (not (>= (HeapSize E) C)))))
  (and (= a!1 A) (not (<= 2 D)) a!2 (not ((_ is O_node) A))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Heap) (D HeapObject) (E Int) ) 
    (=>
      (and
        (inv_main600_3 C B A E)
        (Inv_Heap E D)
        (let ((a!1 (ite (and (not (<= E 0)) (>= (HeapSize C) E))
                (select (HeapContents C) E)
                defObj)))
  (and (= a!1 D) (>= (HeapSize C) E) (not (<= E 0)) (not ((_ is O_node) D))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A HeapObject) (B Int) (C Int) (D Int) (E Heap) ) 
    (=>
      (and
        (inv_main600_3 E D C B)
        (let ((a!1 (ite (and (not (<= B 0)) (>= (HeapSize E) B))
                (select (HeapContents E) B)
                defObj))
      (a!2 (or (<= B 0) (not (>= (HeapSize E) B)))))
  (and (= a!1 A) a!2 (not ((_ is O_node) A))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Heap) (B HeapObject) (C node) (D AllocResHeap) (E Heap) (F Int) (G HeapObject) (H Int) ) 
    (=>
      (and
        (Inv_Heap H G)
        (let ((a!1 (HeapCtor (+ 1 (HeapSize A))
                     (store (HeapContents A) (+ 1 (HeapSize A)) B)))
      (a!3 (ite (and (not (<= H 0)) (>= (HeapSize E) H))
                (select (HeapContents E) H)
                defObj)))
(let ((a!2 (= (AllocResHeap a!1 (+ 1 (HeapSize A))) D)))
  (and (= (HeapCtor 0 ((as const (Array Int HeapObject)) defObj)) A)
       (= 0 F)
       (not (= F H))
       a!2
       (= (AllocResHeap E H) D)
       (= a!3 G)
       (= (O_node C) B)
       (>= (HeapSize E) H)
       (not (<= H 0))
       (not ((_ is O_node) G)))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Heap) (B HeapObject) (C node) (D AllocResHeap) (E HeapObject) (F Heap) (G Int) (H Int) ) 
    (=>
      (and
        (let ((a!1 (HeapCtor (+ 1 (HeapSize A))
                     (store (HeapContents A) (+ 1 (HeapSize A)) B)))
      (a!3 (ite (and (not (<= G 0)) (>= (HeapSize F) G))
                (select (HeapContents F) G)
                defObj))
      (a!4 (or (<= G 0) (not (>= (HeapSize F) G)))))
(let ((a!2 (= (AllocResHeap a!1 (+ 1 (HeapSize A))) D)))
  (and (= (HeapCtor 0 ((as const (Array Int HeapObject)) defObj)) A)
       (= 0 H)
       (not (= H G))
       a!2
       (= (AllocResHeap F G) D)
       (= a!3 E)
       (= (O_node C) B)
       a!4
       (not ((_ is O_node) E)))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A HeapObject) (B node) (C Int) (D node) (E Heap) (F HeapObject) (G Int) (H Heap) (I HeapObject) (J Int) ) 
    (=>
      (and
        (_Glue11 H G J F)
        (Inv_Heap J I)
        (let ((a!1 (ite (and (not (<= J 0)) (>= (HeapSize H) J))
                (HeapCtor (HeapSize H) (store (HeapContents H) J A))
                H))
      (a!2 (ite (and (not (<= J 0)) (>= (HeapSize E) J))
                (select (HeapContents E) J)
                defObj)))
  (and (not ((_ is O_node) I))
       (= (node C G) B)
       (= (getnode F) D)
       (= a!1 E)
       (= (|node::data| D) 1)
       (= (|node::next| D) C)
       (= a!2 I)
       (= (O_node B) A)
       (>= (HeapSize E) J)
       (not (<= J 0))
       ((_ is O_node) F)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A HeapObject) (B node) (C Int) (D node) (E HeapObject) (F Heap) (G HeapObject) (H Int) (I Int) (J Heap) ) 
    (=>
      (and
        (_Glue11 J I H G)
        (let ((a!1 (ite (and (not (<= H 0)) (>= (HeapSize J) H))
                (HeapCtor (HeapSize J) (store (HeapContents J) H A))
                J))
      (a!2 (ite (and (not (<= H 0)) (>= (HeapSize F) H))
                (select (HeapContents F) H)
                defObj))
      (a!3 (or (<= H 0) (not (>= (HeapSize F) H)))))
  (and ((_ is O_node) G)
       (= (node C I) B)
       (= (getnode G) D)
       (= a!1 F)
       (= (|node::data| D) 1)
       (= (|node::next| D) C)
       (= a!2 E)
       (= (O_node B) A)
       a!3
       (not ((_ is O_node) E))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A AllocResHeap) (B HeapObject) (C node) (D Heap) (E Int) (F Int) (G Int) (H Int) (I Heap) (J HeapObject) (K Int) ) 
    (=>
      (and
        (inv_main581_3 I H G F)
        (Inv_Heap K J)
        (let ((a!1 (HeapCtor (+ 1 (HeapSize I))
                     (store (HeapContents I) (+ 1 (HeapSize I)) B)))
      (a!3 (ite (and (not (<= K 0)) (>= (HeapSize D) K))
                (select (HeapContents D) K)
                defObj)))
(let ((a!2 (= (AllocResHeap a!1 (+ 1 (HeapSize I))) A)))
  (and (= 0 E)
       (not (= E K))
       a!2
       (= (AllocResHeap D K) A)
       (= a!3 J)
       (= (O_node C) B)
       (>= (HeapSize D) K)
       (<= 2 H)
       (not (<= K 0))
       (not ((_ is O_node) J)))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A AllocResHeap) (B HeapObject) (C node) (D HeapObject) (E Heap) (F Int) (G Int) (H Int) (I Int) (J Int) (K Heap) ) 
    (=>
      (and
        (inv_main581_3 K J I H)
        (let ((a!1 (HeapCtor (+ 1 (HeapSize K))
                     (store (HeapContents K) (+ 1 (HeapSize K)) B)))
      (a!3 (ite (and (not (<= F 0)) (>= (HeapSize E) F))
                (select (HeapContents E) F)
                defObj))
      (a!4 (or (<= F 0) (not (>= (HeapSize E) F)))))
(let ((a!2 (= (AllocResHeap a!1 (+ 1 (HeapSize K))) A)))
  (and (= 0 G)
       (not (= G F))
       a!2
       (= (AllocResHeap E F) A)
       (= a!3 D)
       (= (O_node C) B)
       (<= 2 J)
       a!4
       (not ((_ is O_node) D)))))
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

(set-logic HORN)

(declare-datatypes ((state_type 0)) (((state_type  (balances (Array Int Int))))))
(declare-datatypes ((abi_type 0)) (((abi_type ))))
(declare-datatypes ((bytes_tuple 0)) (((bytes_tuple  (bytes_tuple_accessor_array (Array Int Int)) (bytes_tuple_accessor_length Int)))))
(declare-datatypes ((ecrecover_input_type 0)) (((ecrecover_input_type  (hash Int) (v Int) (r Int) (s Int)))))
(declare-datatypes ((crypto_type 0)) (((crypto_type  (ecrecover (Array ecrecover_input_type Int)) (keccak256 (Array bytes_tuple Int)) (ripemd160 (Array bytes_tuple Int)) (sha256 (Array bytes_tuple Int))))))
(declare-datatypes ((tx_type 0)) (((tx_type  (block.basefee Int) (block.chainid Int) (block.coinbase Int) (block.difficulty Int) (block.gaslimit Int) (block.number Int) (block.timestamp Int) (blockhash (Array Int Int)) (msg.data bytes_tuple) (msg.sender Int) (msg.sig Int) (msg.value Int) (tx.gasprice Int) (tx.origin Int)))))

(declare-fun |error_target_5_0| ( ) Bool)
(declare-fun |block_9_function_f__40_41_0| ( Int Int abi_type crypto_type tx_type state_type state_type Int Int ) Bool)
(declare-fun |block_5_function_f__40_41_0| ( Int Int abi_type crypto_type tx_type state_type state_type Int Int ) Bool)
(declare-fun |block_11_function_f__40_41_0| ( Int Int abi_type crypto_type tx_type state_type state_type Int Int ) Bool)
(declare-fun |block_7_return_function_f__40_41_0| ( Int Int abi_type crypto_type tx_type state_type state_type Int Int ) Bool)
(declare-fun |implicit_constructor_entry_15_C_41_0| ( Int Int abi_type crypto_type tx_type state_type state_type ) Bool)
(declare-fun |summary_4_function_f__40_41_0| ( Int Int abi_type crypto_type tx_type state_type state_type Int ) Bool)
(declare-fun |contract_initializer_after_init_14_C_41_0| ( Int Int abi_type crypto_type tx_type state_type state_type ) Bool)
(declare-fun |contract_initializer_12_C_41_0| ( Int Int abi_type crypto_type tx_type state_type state_type ) Bool)
(declare-fun |summary_constructor_2_C_41_0| ( Int Int abi_type crypto_type tx_type state_type state_type ) Bool)
(declare-fun |block_8_function_f__40_41_0| ( Int Int abi_type crypto_type tx_type state_type state_type Int Int ) Bool)
(declare-fun |summary_3_function_f__40_41_0| ( Int Int abi_type crypto_type tx_type state_type state_type Int ) Bool)
(declare-fun |block_6_f_39_41_0| ( Int Int abi_type crypto_type tx_type state_type state_type Int Int ) Bool)
(declare-fun |contract_initializer_entry_13_C_41_0| ( Int Int abi_type crypto_type tx_type state_type state_type ) Bool)
(declare-fun |interface_0_C_41_0| ( Int abi_type crypto_type state_type ) Bool)

(assert
  (forall ( (A Int) (B abi_type) (C Int) (D crypto_type) (E Int) (F state_type) (G state_type) (H Int) (I tx_type) ) 
    (=>
      (and
        true
      )
      (block_5_function_f__40_41_0 E H B D I F G A C)
    )
  )
)
(assert
  (forall ( (A Int) (B abi_type) (C Int) (D crypto_type) (E Int) (F state_type) (G state_type) (H Int) (I tx_type) ) 
    (=>
      (and
        (block_5_function_f__40_41_0 E H B D I F G A C)
        (and (= E 0) (= G F))
      )
      (block_6_f_39_41_0 E H B D I F G A C)
    )
  )
)
(assert
  (forall ( (A Int) (B abi_type) (C Int) (D Int) (E crypto_type) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Bool) (R Int) (S state_type) (T state_type) (U Int) (V tx_type) ) 
    (=>
      (and
        (block_6_f_39_41_0 F U B E V S T A C)
        (let ((a!1 (ite (>= H 0)
                ((_ int_to_bv 8) H)
                (bvmul #xff ((_ int_to_bv 8) (* (- 1) H)))))
      (a!2 (ite (>= K 0)
                ((_ int_to_bv 8) K)
                (bvmul #xff ((_ int_to_bv 8) (* (- 1) K))))))
  (and (= R 15)
       (= D M)
       (= A 0)
       (= O 255)
       (= L (ubv_to_int (bvor a!1 a!2)))
       (= J I)
       (= I 240)
       (= H R)
       (= G 1)
       (= C 0)
       (= N D)
       (= K J)
       (= P O)
       (= M L)
       (>= L 0)
       (>= J 0)
       (>= H 0)
       (>= N 0)
       (>= K 0)
       (>= P 0)
       (>= M 0)
       (<= L 255)
       (<= J 255)
       (<= H 255)
       (<= N 255)
       (<= K 255)
       (<= P 255)
       (<= M 255)
       (not Q)
       (= Q (= N P))))
      )
      (block_8_function_f__40_41_0 G U B E V S T A D)
    )
  )
)
(assert
  (forall ( (A Int) (B abi_type) (C Int) (D crypto_type) (E Int) (F state_type) (G state_type) (H Int) (I tx_type) ) 
    (=>
      (and
        (block_8_function_f__40_41_0 E H B D I F G A C)
        true
      )
      (summary_3_function_f__40_41_0 E H B D I F G A)
    )
  )
)
(assert
  (forall ( (A Int) (B abi_type) (C Int) (D crypto_type) (E Int) (F state_type) (G state_type) (H Int) (I tx_type) ) 
    (=>
      (and
        (block_9_function_f__40_41_0 E H B D I F G A C)
        true
      )
      (summary_3_function_f__40_41_0 E H B D I F G A)
    )
  )
)
(assert
  (forall ( (A Int) (B abi_type) (C Int) (D crypto_type) (E Int) (F state_type) (G state_type) (H Int) (I tx_type) ) 
    (=>
      (and
        (block_7_return_function_f__40_41_0 E H B D I F G A C)
        true
      )
      (summary_3_function_f__40_41_0 E H B D I F G A)
    )
  )
)
(assert
  (forall ( (A Int) (B abi_type) (C Int) (D Int) (E crypto_type) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Bool) (S Int) (T Int) (U Int) (V Bool) (W Int) (X state_type) (Y state_type) (Z Int) (A1 tx_type) ) 
    (=>
      (and
        (block_6_f_39_41_0 F Z B E A1 X Y A C)
        (let ((a!1 (ite (>= I 0)
                ((_ int_to_bv 8) I)
                (bvmul #xff ((_ int_to_bv 8) (* (- 1) I)))))
      (a!2 (ite (>= L 0)
                ((_ int_to_bv 8) L)
                (bvmul #xff ((_ int_to_bv 8) (* (- 1) L))))))
  (and (= R (= O Q))
       (= W 15)
       (= A 0)
       (= I W)
       (= C 0)
       (= T 0)
       (= Q P)
       (= O D)
       (= N M)
       (= M (ubv_to_int (bvor a!1 a!2)))
       (= L K)
       (= K J)
       (= J 240)
       (= H 2)
       (= G F)
       (= D N)
       (= S D)
       (= P 255)
       (= U T)
       (>= I 0)
       (>= Q 0)
       (>= O 0)
       (>= N 0)
       (>= M 0)
       (>= L 0)
       (>= K 0)
       (>= S 0)
       (>= U 0)
       (<= I 255)
       (<= Q 255)
       (<= O 255)
       (<= N 255)
       (<= M 255)
       (<= L 255)
       (<= K 255)
       (<= S 255)
       (<= U 255)
       (not V)
       (= V (= S U))))
      )
      (block_9_function_f__40_41_0 H Z B E A1 X Y A D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C abi_type) (D Int) (E Int) (F crypto_type) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Bool) (T Int) (U Int) (V Int) (W Bool) (X Int) (Y Int) (Z state_type) (A1 state_type) (B1 Int) (C1 tx_type) ) 
    (=>
      (and
        (block_6_f_39_41_0 G B1 C F C1 Z A1 A D)
        (let ((a!1 (ite (>= J 0)
                ((_ int_to_bv 8) J)
                (bvmul #xff ((_ int_to_bv 8) (* (- 1) J)))))
      (a!2 (ite (>= M 0)
                ((_ int_to_bv 8) M)
                (bvmul #xff ((_ int_to_bv 8) (* (- 1) M))))))
  (and (= W (= T V))
       (= B X)
       (= Y 15)
       (= K 240)
       (= H G)
       (= E O)
       (= D 0)
       (= V U)
       (= Q 255)
       (= P E)
       (= O N)
       (= N (ubv_to_int (bvor a!1 a!2)))
       (= M L)
       (= L K)
       (= J Y)
       (= I H)
       (= A 0)
       (= U 0)
       (= R Q)
       (= X E)
       (= T E)
       (>= V 0)
       (>= P 0)
       (>= O 0)
       (>= N 0)
       (>= M 0)
       (>= L 0)
       (>= J 0)
       (>= R 0)
       (>= X 0)
       (>= T 0)
       (<= V 255)
       (<= P 255)
       (<= O 255)
       (<= N 255)
       (<= M 255)
       (<= L 255)
       (<= J 255)
       (<= R 255)
       (<= X 255)
       (<= T 255)
       (= S (= P R))))
      )
      (block_7_return_function_f__40_41_0 I B1 C F C1 Z A1 B E)
    )
  )
)
(assert
  (forall ( (A Int) (B abi_type) (C Int) (D crypto_type) (E Int) (F state_type) (G state_type) (H Int) (I tx_type) ) 
    (=>
      (and
        true
      )
      (block_11_function_f__40_41_0 E H B D I F G A C)
    )
  )
)
(assert
  (forall ( (A Int) (B abi_type) (C Int) (D crypto_type) (E Int) (F Int) (G Int) (H state_type) (I state_type) (J state_type) (K state_type) (L Int) (M tx_type) ) 
    (=>
      (and
        (block_11_function_f__40_41_0 E L B D M H I A C)
        (summary_3_function_f__40_41_0 F L B D M J K A)
        (let ((a!1 (= (select (bytes_tuple_accessor_array (msg.data M)) 3) 240))
      (a!2 (= (select (bytes_tuple_accessor_array (msg.data M)) 2) 31))
      (a!3 (= (select (bytes_tuple_accessor_array (msg.data M)) 1) 18))
      (a!4 (= (select (bytes_tuple_accessor_array (msg.data M)) 0) 38))
      (a!5 (>= (+ (select (balances I) L) G) 0))
      (a!6 (<= (+ (select (balances I) L) G)
               115792089237316195423570985008687907853269984665640564039457584007913129639935))
      (a!7 (store (balances I) L (+ (select (balances I) L) G))))
  (and (= I H)
       a!1
       a!2
       a!3
       a!4
       (= (msg.value M) 0)
       (= (msg.sig M) 638722032)
       (= E 0)
       (>= (tx.origin M) 0)
       (>= (tx.gasprice M) 0)
       (>= (msg.value M) 0)
       (>= (msg.sender M) 0)
       (>= (block.timestamp M) 0)
       (>= (block.number M) 0)
       (>= (block.gaslimit M) 0)
       (>= (block.difficulty M) 0)
       (>= (block.coinbase M) 0)
       (>= (block.chainid M) 0)
       (>= (block.basefee M) 0)
       (>= (bytes_tuple_accessor_length (msg.data M)) 4)
       a!5
       (>= G (msg.value M))
       (<= (tx.origin M) 1461501637330902918203684832716283019655932542975)
       (<= (tx.gasprice M)
           115792089237316195423570985008687907853269984665640564039457584007913129639935)
       (<= (msg.value M)
           115792089237316195423570985008687907853269984665640564039457584007913129639935)
       (<= (msg.sender M) 1461501637330902918203684832716283019655932542975)
       (<= (block.timestamp M)
           115792089237316195423570985008687907853269984665640564039457584007913129639935)
       (<= (block.number M)
           115792089237316195423570985008687907853269984665640564039457584007913129639935)
       (<= (block.gaslimit M)
           115792089237316195423570985008687907853269984665640564039457584007913129639935)
       (<= (block.difficulty M)
           115792089237316195423570985008687907853269984665640564039457584007913129639935)
       (<= (block.coinbase M) 1461501637330902918203684832716283019655932542975)
       (<= (block.chainid M)
           115792089237316195423570985008687907853269984665640564039457584007913129639935)
       (<= (block.basefee M)
           115792089237316195423570985008687907853269984665640564039457584007913129639935)
       a!6
       (= J (state_type a!7))))
      )
      (summary_4_function_f__40_41_0 F L B D M H K A)
    )
  )
)
(assert
  (forall ( (A Int) (B abi_type) (C crypto_type) (D Int) (E state_type) (F state_type) (G Int) (H tx_type) ) 
    (=>
      (and
        (summary_4_function_f__40_41_0 D G B C H E F A)
        (interface_0_C_41_0 G B C E)
        (= D 0)
      )
      (interface_0_C_41_0 G B C F)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D state_type) (E state_type) (F Int) (G tx_type) ) 
    (=>
      (and
        (summary_constructor_2_C_41_0 C F A B G D E)
        (and (= C 0)
     (>= (tx.origin G) 0)
     (>= (tx.gasprice G) 0)
     (>= (msg.value G) 0)
     (>= (msg.sender G) 0)
     (>= (block.timestamp G) 0)
     (>= (block.number G) 0)
     (>= (block.gaslimit G) 0)
     (>= (block.difficulty G) 0)
     (>= (block.coinbase G) 0)
     (>= (block.chainid G) 0)
     (>= (block.basefee G) 0)
     (<= (tx.origin G) 1461501637330902918203684832716283019655932542975)
     (<= (tx.gasprice G)
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= (msg.value G)
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= (msg.sender G) 1461501637330902918203684832716283019655932542975)
     (<= (block.timestamp G)
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= (block.number G)
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= (block.gaslimit G)
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= (block.difficulty G)
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= (block.coinbase G) 1461501637330902918203684832716283019655932542975)
     (<= (block.chainid G)
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= (block.basefee G)
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (= (msg.value G) 0))
      )
      (interface_0_C_41_0 F A B E)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D state_type) (E state_type) (F Int) (G tx_type) ) 
    (=>
      (and
        (and (= C 0) (= E D))
      )
      (contract_initializer_entry_13_C_41_0 C F A B G D E)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D state_type) (E state_type) (F Int) (G tx_type) ) 
    (=>
      (and
        (contract_initializer_entry_13_C_41_0 C F A B G D E)
        true
      )
      (contract_initializer_after_init_14_C_41_0 C F A B G D E)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D state_type) (E state_type) (F Int) (G tx_type) ) 
    (=>
      (and
        (contract_initializer_after_init_14_C_41_0 C F A B G D E)
        true
      )
      (contract_initializer_12_C_41_0 C F A B G D E)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D state_type) (E state_type) (F Int) (G tx_type) ) 
    (=>
      (and
        (and (= C 0) (>= (select (balances E) F) (msg.value G)) (= E D))
      )
      (implicit_constructor_entry_15_C_41_0 C F A B G D E)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D Int) (E state_type) (F state_type) (G state_type) (H Int) (I tx_type) ) 
    (=>
      (and
        (implicit_constructor_entry_15_C_41_0 C H A B I E F)
        (contract_initializer_12_C_41_0 D H A B I F G)
        (not (<= D 0))
      )
      (summary_constructor_2_C_41_0 D H A B I E G)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D Int) (E state_type) (F state_type) (G state_type) (H Int) (I tx_type) ) 
    (=>
      (and
        (contract_initializer_12_C_41_0 D H A B I F G)
        (implicit_constructor_entry_15_C_41_0 C H A B I E F)
        (= D 0)
      )
      (summary_constructor_2_C_41_0 D H A B I E G)
    )
  )
)
(assert
  (forall ( (A Int) (B abi_type) (C crypto_type) (D Int) (E state_type) (F state_type) (G Int) (H tx_type) ) 
    (=>
      (and
        (summary_4_function_f__40_41_0 D G B C H E F A)
        (interface_0_C_41_0 G B C E)
        (= D 2)
      )
      error_target_5_0
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        error_target_5_0
        true
      )
      false
    )
  )
)

(check-sat)
(exit)

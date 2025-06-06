(set-logic HORN)

(declare-datatypes ((state_type 0)) (((state_type  (balances (Array Int Int))))))
(declare-datatypes ((abi_type 0)) (((abi_type ))))
(declare-datatypes ((bytes_tuple 0)) (((bytes_tuple  (bytes_tuple_accessor_array (Array Int Int)) (bytes_tuple_accessor_length Int)))))
(declare-datatypes ((ecrecover_input_type 0)) (((ecrecover_input_type  (hash Int) (v Int) (r Int) (s Int)))))
(declare-datatypes ((crypto_type 0)) (((crypto_type  (ecrecover (Array ecrecover_input_type Int)) (keccak256 (Array bytes_tuple Int)) (ripemd160 (Array bytes_tuple Int)) (sha256 (Array bytes_tuple Int))))))
(declare-datatypes ((tx_type 0)) (((tx_type  (block.basefee Int) (block.chainid Int) (block.coinbase Int) (block.difficulty Int) (block.gaslimit Int) (block.number Int) (block.timestamp Int) (blockhash (Array Int Int)) (msg.data bytes_tuple) (msg.sender Int) (msg.sig Int) (msg.value Int) (tx.gasprice Int) (tx.origin Int)))))

(declare-fun |block_16_try_clause_27f_27_65_0| ( Int Int abi_type crypto_type tx_type state_type state_type Int Bool bytes_tuple bytes_tuple ) Bool)
(declare-fun |error_target_5_0| ( ) Bool)
(declare-fun |block_22_function_f__64_65_0| ( Int Int abi_type crypto_type tx_type state_type state_type Int Bool bytes_tuple bytes_tuple ) Bool)
(declare-fun |contract_initializer_23_C_65_0| ( Int Int abi_type crypto_type tx_type state_type state_type ) Bool)
(declare-fun |block_7_function_g__4_65_0| ( Int Int abi_type crypto_type tx_type state_type state_type ) Bool)
(declare-fun |contract_initializer_after_init_25_C_65_0| ( Int Int abi_type crypto_type tx_type state_type state_type ) Bool)
(declare-fun |block_11_function_f__64_65_0| ( Int Int abi_type crypto_type tx_type state_type state_type Int Bool bytes_tuple bytes_tuple ) Bool)
(declare-fun |contract_initializer_entry_24_C_65_0| ( Int Int abi_type crypto_type tx_type state_type state_type ) Bool)
(declare-fun |summary_3_function_g__4_65_0| ( Int Int abi_type crypto_type tx_type state_type state_type ) Bool)
(declare-fun |block_9_return_function_g__4_65_0| ( Int Int abi_type crypto_type tx_type state_type state_type ) Bool)
(declare-fun |block_12_f_63_65_0| ( Int Int abi_type crypto_type tx_type state_type state_type Int Bool bytes_tuple bytes_tuple ) Bool)
(declare-fun |block_20_function_f__64_65_0| ( Int Int abi_type crypto_type tx_type state_type state_type Int Bool bytes_tuple bytes_tuple ) Bool)
(declare-fun |summary_6_function_f__64_65_0| ( Int Int abi_type crypto_type tx_type state_type state_type ) Bool)
(declare-fun |block_18_try_clause_45f_45_65_0| ( Int Int abi_type crypto_type tx_type state_type state_type Int Bool bytes_tuple bytes_tuple ) Bool)
(declare-fun |summary_19_function_g__4_65_0| ( Int Int abi_type crypto_type tx_type state_type state_type ) Bool)
(declare-fun |implicit_constructor_entry_26_C_65_0| ( Int Int abi_type crypto_type tx_type state_type state_type ) Bool)
(declare-fun |interface_0_C_65_0| ( Int abi_type crypto_type state_type ) Bool)
(declare-fun |block_17_try_clause_36f_36_65_0| ( Int Int abi_type crypto_type tx_type state_type state_type Int Bool bytes_tuple bytes_tuple ) Bool)
(declare-fun |block_8_g_3_65_0| ( Int Int abi_type crypto_type tx_type state_type state_type ) Bool)
(declare-fun |summary_5_function_f__64_65_0| ( Int Int abi_type crypto_type tx_type state_type state_type ) Bool)
(declare-fun |block_13_return_function_f__64_65_0| ( Int Int abi_type crypto_type tx_type state_type state_type Int Bool bytes_tuple bytes_tuple ) Bool)
(declare-fun |block_10_function_g__4_65_0| ( Int Int abi_type crypto_type tx_type state_type state_type ) Bool)
(declare-fun |block_21_function_f__64_65_0| ( Int Int abi_type crypto_type tx_type state_type state_type Int Bool bytes_tuple bytes_tuple ) Bool)
(declare-fun |block_14_try_header_f_46_65_0| ( Int Int abi_type crypto_type tx_type state_type state_type Int Bool bytes_tuple bytes_tuple ) Bool)
(declare-fun |summary_constructor_2_C_65_0| ( Int Int abi_type crypto_type tx_type state_type state_type ) Bool)
(declare-fun |block_15_f_63_65_0| ( Int Int abi_type crypto_type tx_type state_type state_type Int Bool bytes_tuple bytes_tuple ) Bool)
(declare-fun |summary_4_function_g__4_65_0| ( Int Int abi_type crypto_type tx_type state_type state_type ) Bool)

(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D state_type) (E state_type) (F Int) (G tx_type) ) 
    (=>
      (and
        true
      )
      (block_7_function_g__4_65_0 C F A B G D E)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D state_type) (E state_type) (F Int) (G tx_type) ) 
    (=>
      (and
        (block_7_function_g__4_65_0 C F A B G D E)
        (and (= C 0) (= E D))
      )
      (block_8_g_3_65_0 C F A B G D E)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D state_type) (E state_type) (F Int) (G tx_type) ) 
    (=>
      (and
        (block_8_g_3_65_0 C F A B G D E)
        true
      )
      (block_9_return_function_g__4_65_0 C F A B G D E)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D state_type) (E state_type) (F Int) (G tx_type) ) 
    (=>
      (and
        (block_9_return_function_g__4_65_0 C F A B G D E)
        true
      )
      (summary_3_function_g__4_65_0 C F A B G D E)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D state_type) (E state_type) (F Int) (G tx_type) ) 
    (=>
      (and
        true
      )
      (block_10_function_g__4_65_0 C F A B G D E)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D Int) (E Int) (F state_type) (G state_type) (H state_type) (I state_type) (J Int) (K tx_type) ) 
    (=>
      (and
        (block_10_function_g__4_65_0 C J A B K F G)
        (summary_3_function_g__4_65_0 D J A B K H I)
        (let ((a!1 (= (select (bytes_tuple_accessor_array (msg.data K)) 3) 142))
      (a!2 (= (select (bytes_tuple_accessor_array (msg.data K)) 2) 155))
      (a!3 (= (select (bytes_tuple_accessor_array (msg.data K)) 1) 23))
      (a!4 (= (select (bytes_tuple_accessor_array (msg.data K)) 0) 226))
      (a!5 (>= (+ (select (balances G) J) E) 0))
      (a!6 (<= (+ (select (balances G) J) E)
               115792089237316195423570985008687907853269984665640564039457584007913129639935))
      (a!7 (store (balances G) J (+ (select (balances G) J) E))))
  (and (= G F)
       a!1
       a!2
       a!3
       a!4
       (= (msg.value K) 0)
       (= (msg.sig K) 3793197966)
       (= C 0)
       (>= (tx.origin K) 0)
       (>= (tx.gasprice K) 0)
       (>= (msg.value K) 0)
       (>= (msg.sender K) 0)
       (>= (block.timestamp K) 0)
       (>= (block.number K) 0)
       (>= (block.gaslimit K) 0)
       (>= (block.difficulty K) 0)
       (>= (block.coinbase K) 0)
       (>= (block.chainid K) 0)
       (>= (block.basefee K) 0)
       (>= (bytes_tuple_accessor_length (msg.data K)) 4)
       a!5
       (>= E (msg.value K))
       (<= (tx.origin K) 1461501637330902918203684832716283019655932542975)
       (<= (tx.gasprice K)
           115792089237316195423570985008687907853269984665640564039457584007913129639935)
       (<= (msg.value K)
           115792089237316195423570985008687907853269984665640564039457584007913129639935)
       (<= (msg.sender K) 1461501637330902918203684832716283019655932542975)
       (<= (block.timestamp K)
           115792089237316195423570985008687907853269984665640564039457584007913129639935)
       (<= (block.number K)
           115792089237316195423570985008687907853269984665640564039457584007913129639935)
       (<= (block.gaslimit K)
           115792089237316195423570985008687907853269984665640564039457584007913129639935)
       (<= (block.difficulty K)
           115792089237316195423570985008687907853269984665640564039457584007913129639935)
       (<= (block.coinbase K) 1461501637330902918203684832716283019655932542975)
       (<= (block.chainid K)
           115792089237316195423570985008687907853269984665640564039457584007913129639935)
       (<= (block.basefee K)
           115792089237316195423570985008687907853269984665640564039457584007913129639935)
       a!6
       (= H (state_type a!7))))
      )
      (summary_4_function_g__4_65_0 D J A B K F I)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D state_type) (E state_type) (F Int) (G tx_type) ) 
    (=>
      (and
        (summary_4_function_g__4_65_0 C F A B G D E)
        (interface_0_C_65_0 F A B D)
        (= C 0)
      )
      (interface_0_C_65_0 F A B E)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D state_type) (E state_type) (F Int) (G tx_type) ) 
    (=>
      (and
        (summary_6_function_f__64_65_0 C F A B G D E)
        (interface_0_C_65_0 F A B D)
        (= C 0)
      )
      (interface_0_C_65_0 F A B E)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D state_type) (E state_type) (F Int) (G tx_type) ) 
    (=>
      (and
        (summary_constructor_2_C_65_0 C F A B G D E)
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
      (interface_0_C_65_0 F A B E)
    )
  )
)
(assert
  (forall ( (A bytes_tuple) (B bytes_tuple) (C abi_type) (D crypto_type) (E Int) (F state_type) (G state_type) (H Bool) (I Int) (J tx_type) (K Int) ) 
    (=>
      (and
        true
      )
      (block_11_function_f__64_65_0 E I C D J F G K H A B)
    )
  )
)
(assert
  (forall ( (A bytes_tuple) (B bytes_tuple) (C abi_type) (D crypto_type) (E Int) (F state_type) (G state_type) (H Bool) (I Int) (J tx_type) (K Int) ) 
    (=>
      (and
        (block_11_function_f__64_65_0 E I C D J F G K H A B)
        (and (= E 0) (= G F))
      )
      (block_12_f_63_65_0 E I C D J F G K H A B)
    )
  )
)
(assert
  (forall ( (A bytes_tuple) (B bytes_tuple) (C abi_type) (D crypto_type) (E Int) (F Bool) (G Int) (H state_type) (I state_type) (J Bool) (K Bool) (L Int) (M tx_type) (N Int) (O Int) ) 
    (=>
      (and
        (block_12_f_63_65_0 E L C D M H I N J A B)
        (and (= B (bytes_tuple ((as const (Array Int Int)) 0) 0))
     (= K F)
     (= O G)
     (= G 0)
     (= N 0)
     (not F)
     (not J)
     (= A (bytes_tuple ((as const (Array Int Int)) 0) 0)))
      )
      (block_14_try_header_f_46_65_0 E L C D M H I O K A B)
    )
  )
)
(assert
  (forall ( (A bytes_tuple) (B bytes_tuple) (C abi_type) (D crypto_type) (E Int) (F Int) (G state_type) (H state_type) (I Bool) (J Int) (K tx_type) (L Int) ) 
    (=>
      (and
        (block_14_try_header_f_46_65_0 E J C D K G H L I A B)
        (= F J)
      )
      (block_17_try_clause_36f_36_65_0 E J C D K G H L I A B)
    )
  )
)
(assert
  (forall ( (A bytes_tuple) (B bytes_tuple) (C abi_type) (D crypto_type) (E Int) (F Int) (G state_type) (H state_type) (I Bool) (J Int) (K tx_type) (L Int) ) 
    (=>
      (and
        (block_14_try_header_f_46_65_0 E J C D K G H L I A B)
        (= F J)
      )
      (block_18_try_clause_45f_45_65_0 E J C D K G H L I A B)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D state_type) (E state_type) (F Int) (G tx_type) ) 
    (=>
      (and
        (summary_3_function_g__4_65_0 C F A B G D E)
        true
      )
      (summary_19_function_g__4_65_0 C F A B G D E)
    )
  )
)
(assert
  (forall ( (A bytes_tuple) (B bytes_tuple) (C abi_type) (D crypto_type) (E Int) (F Int) (G Int) (H state_type) (I state_type) (J Bool) (K Int) (L tx_type) (M tx_type) (N tx_type) (O Int) (v_15 state_type) ) 
    (=>
      (and
        (block_14_try_header_f_46_65_0 E K C D L H I O J A B)
        (summary_19_function_g__4_65_0 F G C D M I v_15)
        (let ((a!1 (= (select (bytes_tuple_accessor_array (msg.data M)) 3) 142))
      (a!2 (= (select (bytes_tuple_accessor_array (msg.data M)) 2) 155))
      (a!3 (= (select (bytes_tuple_accessor_array (msg.data M)) 1) 23))
      (a!4 (= (select (bytes_tuple_accessor_array (msg.data M)) 0) 226)))
  (and (= v_15 I)
       a!1
       a!2
       a!3
       a!4
       (= (tx.origin M) (tx.origin L))
       (= (msg.value M) 0)
       (= (msg.sig M) 3793197966)
       (= (msg.sender M) K)
       (= G K)
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
       (not (<= F 0))
       (= L N)))
      )
      (summary_5_function_f__64_65_0 F K C D L H I)
    )
  )
)
(assert
  (forall ( (A bytes_tuple) (B bytes_tuple) (C abi_type) (D crypto_type) (E Int) (F state_type) (G state_type) (H Bool) (I Int) (J tx_type) (K Int) ) 
    (=>
      (and
        (block_20_function_f__64_65_0 E I C D J F G K H A B)
        true
      )
      (summary_5_function_f__64_65_0 E I C D J F G)
    )
  )
)
(assert
  (forall ( (A bytes_tuple) (B bytes_tuple) (C abi_type) (D crypto_type) (E Int) (F state_type) (G state_type) (H Bool) (I Int) (J tx_type) (K Int) ) 
    (=>
      (and
        (block_21_function_f__64_65_0 E I C D J F G K H A B)
        true
      )
      (summary_5_function_f__64_65_0 E I C D J F G)
    )
  )
)
(assert
  (forall ( (A bytes_tuple) (B bytes_tuple) (C abi_type) (D crypto_type) (E Int) (F state_type) (G state_type) (H Bool) (I Int) (J tx_type) (K Int) ) 
    (=>
      (and
        (block_13_return_function_f__64_65_0 E I C D J F G K H A B)
        true
      )
      (summary_5_function_f__64_65_0 E I C D J F G)
    )
  )
)
(assert
  (forall ( (A bytes_tuple) (B bytes_tuple) (C abi_type) (D crypto_type) (E Int) (F Int) (G Int) (H state_type) (I state_type) (J Bool) (K Int) (L tx_type) (M tx_type) (N tx_type) (O Int) (v_15 state_type) ) 
    (=>
      (and
        (block_14_try_header_f_46_65_0 E K C D L H I O J A B)
        (summary_19_function_g__4_65_0 F G C D M I v_15)
        (let ((a!1 (= (select (bytes_tuple_accessor_array (msg.data M)) 3) 142))
      (a!2 (= (select (bytes_tuple_accessor_array (msg.data M)) 2) 155))
      (a!3 (= (select (bytes_tuple_accessor_array (msg.data M)) 1) 23))
      (a!4 (= (select (bytes_tuple_accessor_array (msg.data M)) 0) 226)))
  (and (= v_15 I)
       a!1
       a!2
       a!3
       a!4
       (= (tx.origin M) (tx.origin L))
       (= (msg.value M) 0)
       (= (msg.sig M) 3793197966)
       (= (msg.sender M) K)
       (= G K)
       (= F 0)
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
       (= L N)))
      )
      (block_16_try_clause_27f_27_65_0 F K C D L H I O J A B)
    )
  )
)
(assert
  (forall ( (A bytes_tuple) (B bytes_tuple) (C abi_type) (D crypto_type) (E Int) (F Bool) (G Bool) (H Bool) (I Int) (J Int) (K Int) (L state_type) (M state_type) (N Bool) (O Bool) (P Int) (Q tx_type) (R Int) (S Int) ) 
    (=>
      (and
        (block_16_try_clause_27f_27_65_0 E P C D Q L M R N A B)
        (and (= H G)
     (= O H)
     (= S K)
     (= K J)
     (= J 1)
     (= I R)
     (>= K 0)
     (>= I 0)
     (<= K
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= I
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (= G true)
     (= F N))
      )
      (block_15_f_63_65_0 E P C D Q L M S O A B)
    )
  )
)
(assert
  (forall ( (A bytes_tuple) (B bytes_tuple) (C abi_type) (D crypto_type) (E Int) (F Int) (G Int) (H Int) (I state_type) (J state_type) (K Bool) (L Int) (M tx_type) (N Int) (O Int) ) 
    (=>
      (and
        (block_17_try_clause_36f_36_65_0 E L C D M I J N K A B)
        (and (= O H)
     (= G 2)
     (= F N)
     (>= H 0)
     (>= F 0)
     (<= H
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= F
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (= H G))
      )
      (block_15_f_63_65_0 E L C D M I J O K A B)
    )
  )
)
(assert
  (forall ( (A bytes_tuple) (B bytes_tuple) (C abi_type) (D crypto_type) (E Int) (F Int) (G Int) (H Int) (I state_type) (J state_type) (K Bool) (L Int) (M tx_type) (N Int) (O Int) ) 
    (=>
      (and
        (block_18_try_clause_45f_45_65_0 E L C D M I J N K A B)
        (and (= O H)
     (= G 3)
     (= F N)
     (>= H 0)
     (>= F 0)
     (<= H
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= F
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (= H G))
      )
      (block_15_f_63_65_0 E L C D M I J O K A B)
    )
  )
)
(assert
  (forall ( (A bytes_tuple) (B bytes_tuple) (C abi_type) (D crypto_type) (E Int) (F Int) (G Int) (H Int) (I Bool) (J Int) (K Int) (L Bool) (M Bool) (N state_type) (O state_type) (P Bool) (Q Int) (R tx_type) (S Int) ) 
    (=>
      (and
        (block_15_f_63_65_0 E Q C D R N O S P A B)
        (and (not (= (<= K J) L))
     (= M (and L I))
     (= G S)
     (= F 1)
     (= K 4)
     (= J S)
     (= H 0)
     (>= G 0)
     (<= G
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (or (not I)
         (and (<= J
                  115792089237316195423570985008687907853269984665640564039457584007913129639935)
              (>= J 0)))
     (not M)
     (not (= (<= G H) I)))
      )
      (block_20_function_f__64_65_0 F Q C D R N O S P A B)
    )
  )
)
(assert
  (forall ( (A bytes_tuple) (B bytes_tuple) (C abi_type) (D crypto_type) (E Int) (F Int) (G Int) (H Int) (I Int) (J Bool) (K Int) (L Int) (M Bool) (N Bool) (O Int) (P Int) (Q Bool) (R state_type) (S state_type) (T Bool) (U Int) (V tx_type) (W Int) ) 
    (=>
      (and
        (block_15_f_63_65_0 E U C D V R S W T A B)
        (and (not (= (<= L K) M))
     (= N (and J M))
     (= Q (= O P))
     (= H W)
     (= K W)
     (= P 0)
     (= G 2)
     (= I 0)
     (= F E)
     (= O W)
     (= L 4)
     (>= H 0)
     (>= O 0)
     (<= H
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= O
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (or (not J)
         (and (<= K
                  115792089237316195423570985008687907853269984665640564039457584007913129639935)
              (>= K 0)))
     (not Q)
     (not (= (<= H I) J)))
      )
      (block_21_function_f__64_65_0 G U C D V R S W T A B)
    )
  )
)
(assert
  (forall ( (A bytes_tuple) (B bytes_tuple) (C abi_type) (D crypto_type) (E Int) (F Int) (G Int) (H Int) (I Int) (J Bool) (K Int) (L Int) (M Bool) (N Bool) (O Int) (P Int) (Q Bool) (R state_type) (S state_type) (T Bool) (U Int) (V tx_type) (W Int) ) 
    (=>
      (and
        (block_15_f_63_65_0 E U C D V R S W T A B)
        (and (not (= (<= L K) M))
     (= N (and J M))
     (= Q (= O P))
     (= H W)
     (= K W)
     (= P 0)
     (= G F)
     (= I 0)
     (= F E)
     (= O W)
     (= L 4)
     (>= H 0)
     (>= O 0)
     (<= H
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= O
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (or (not J)
         (and (<= K
                  115792089237316195423570985008687907853269984665640564039457584007913129639935)
              (>= K 0)))
     (not (= (<= H I) J)))
      )
      (block_13_return_function_f__64_65_0 G U C D V R S W T A B)
    )
  )
)
(assert
  (forall ( (A bytes_tuple) (B bytes_tuple) (C abi_type) (D crypto_type) (E Int) (F state_type) (G state_type) (H Bool) (I Int) (J tx_type) (K Int) ) 
    (=>
      (and
        true
      )
      (block_22_function_f__64_65_0 E I C D J F G K H A B)
    )
  )
)
(assert
  (forall ( (A bytes_tuple) (B bytes_tuple) (C abi_type) (D crypto_type) (E Int) (F Int) (G Int) (H state_type) (I state_type) (J state_type) (K state_type) (L Bool) (M Int) (N tx_type) (O Int) ) 
    (=>
      (and
        (block_22_function_f__64_65_0 E M C D N H I O L A B)
        (summary_5_function_f__64_65_0 F M C D N J K)
        (let ((a!1 (= (select (bytes_tuple_accessor_array (msg.data N)) 3) 240))
      (a!2 (= (select (bytes_tuple_accessor_array (msg.data N)) 2) 31))
      (a!3 (= (select (bytes_tuple_accessor_array (msg.data N)) 1) 18))
      (a!4 (= (select (bytes_tuple_accessor_array (msg.data N)) 0) 38))
      (a!5 (>= (+ (select (balances I) M) G) 0))
      (a!6 (<= (+ (select (balances I) M) G)
               115792089237316195423570985008687907853269984665640564039457584007913129639935))
      (a!7 (store (balances I) M (+ (select (balances I) M) G))))
  (and (= I H)
       a!1
       a!2
       a!3
       a!4
       (= (msg.value N) 0)
       (= (msg.sig N) 638722032)
       (= E 0)
       (>= (tx.origin N) 0)
       (>= (tx.gasprice N) 0)
       (>= (msg.value N) 0)
       (>= (msg.sender N) 0)
       (>= (block.timestamp N) 0)
       (>= (block.number N) 0)
       (>= (block.gaslimit N) 0)
       (>= (block.difficulty N) 0)
       (>= (block.coinbase N) 0)
       (>= (block.chainid N) 0)
       (>= (block.basefee N) 0)
       (>= (bytes_tuple_accessor_length (msg.data N)) 4)
       a!5
       (>= G (msg.value N))
       (<= (tx.origin N) 1461501637330902918203684832716283019655932542975)
       (<= (tx.gasprice N)
           115792089237316195423570985008687907853269984665640564039457584007913129639935)
       (<= (msg.value N)
           115792089237316195423570985008687907853269984665640564039457584007913129639935)
       (<= (msg.sender N) 1461501637330902918203684832716283019655932542975)
       (<= (block.timestamp N)
           115792089237316195423570985008687907853269984665640564039457584007913129639935)
       (<= (block.number N)
           115792089237316195423570985008687907853269984665640564039457584007913129639935)
       (<= (block.gaslimit N)
           115792089237316195423570985008687907853269984665640564039457584007913129639935)
       (<= (block.difficulty N)
           115792089237316195423570985008687907853269984665640564039457584007913129639935)
       (<= (block.coinbase N) 1461501637330902918203684832716283019655932542975)
       (<= (block.chainid N)
           115792089237316195423570985008687907853269984665640564039457584007913129639935)
       (<= (block.basefee N)
           115792089237316195423570985008687907853269984665640564039457584007913129639935)
       a!6
       (= J (state_type a!7))))
      )
      (summary_6_function_f__64_65_0 F M C D N H K)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D state_type) (E state_type) (F Int) (G tx_type) ) 
    (=>
      (and
        (and (= C 0) (= E D))
      )
      (contract_initializer_entry_24_C_65_0 C F A B G D E)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D state_type) (E state_type) (F Int) (G tx_type) ) 
    (=>
      (and
        (contract_initializer_entry_24_C_65_0 C F A B G D E)
        true
      )
      (contract_initializer_after_init_25_C_65_0 C F A B G D E)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D state_type) (E state_type) (F Int) (G tx_type) ) 
    (=>
      (and
        (contract_initializer_after_init_25_C_65_0 C F A B G D E)
        true
      )
      (contract_initializer_23_C_65_0 C F A B G D E)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D state_type) (E state_type) (F Int) (G tx_type) ) 
    (=>
      (and
        (and (= C 0) (>= (select (balances E) F) (msg.value G)) (= E D))
      )
      (implicit_constructor_entry_26_C_65_0 C F A B G D E)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D Int) (E state_type) (F state_type) (G state_type) (H Int) (I tx_type) ) 
    (=>
      (and
        (implicit_constructor_entry_26_C_65_0 C H A B I E F)
        (contract_initializer_23_C_65_0 D H A B I F G)
        (not (<= D 0))
      )
      (summary_constructor_2_C_65_0 D H A B I E G)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D Int) (E state_type) (F state_type) (G state_type) (H Int) (I tx_type) ) 
    (=>
      (and
        (contract_initializer_23_C_65_0 D H A B I F G)
        (implicit_constructor_entry_26_C_65_0 C H A B I E F)
        (= D 0)
      )
      (summary_constructor_2_C_65_0 D H A B I E G)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D state_type) (E state_type) (F Int) (G tx_type) ) 
    (=>
      (and
        (summary_6_function_f__64_65_0 C F A B G D E)
        (interface_0_C_65_0 F A B D)
        (= C 2)
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

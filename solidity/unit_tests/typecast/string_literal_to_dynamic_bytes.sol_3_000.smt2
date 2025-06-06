(set-logic HORN)

(declare-datatypes ((state_type 0)) (((state_type  (balances (Array Int Int))))))
(declare-datatypes ((abi_type 0)) (((abi_type ))))
(declare-datatypes ((bytes_tuple 0)) (((bytes_tuple  (bytes_tuple_accessor_array (Array Int Int)) (bytes_tuple_accessor_length Int)))))
(declare-datatypes ((ecrecover_input_type 0)) (((ecrecover_input_type  (hash Int) (v Int) (r Int) (s Int)))))
(declare-datatypes ((crypto_type 0)) (((crypto_type  (ecrecover (Array ecrecover_input_type Int)) (keccak256 (Array bytes_tuple Int)) (ripemd160 (Array bytes_tuple Int)) (sha256 (Array bytes_tuple Int))))))
(declare-datatypes ((tx_type 0)) (((tx_type  (block.basefee Int) (block.chainid Int) (block.coinbase Int) (block.difficulty Int) (block.gaslimit Int) (block.number Int) (block.timestamp Int) (blockhash (Array Int Int)) (msg.data bytes_tuple) (msg.sender Int) (msg.sig Int) (msg.value Int) (tx.gasprice Int) (tx.origin Int)))))

(declare-fun |error_target_9_0| ( ) Bool)
(declare-fun |block_5_function_f__46_47_0| ( Int Int abi_type crypto_type tx_type state_type state_type bytes_tuple ) Bool)
(declare-fun |block_12_function_f__46_47_0| ( Int Int abi_type crypto_type tx_type state_type state_type bytes_tuple ) Bool)
(declare-fun |summary_4_function_f__46_47_0| ( Int Int abi_type crypto_type tx_type state_type state_type ) Bool)
(declare-fun |contract_initializer_14_C_47_0| ( Int Int abi_type crypto_type tx_type state_type state_type ) Bool)
(declare-fun |summary_constructor_2_C_47_0| ( Int Int abi_type crypto_type tx_type state_type state_type ) Bool)
(declare-fun |contract_initializer_after_init_16_C_47_0| ( Int Int abi_type crypto_type tx_type state_type state_type ) Bool)
(declare-fun |block_7_return_function_f__46_47_0| ( Int Int abi_type crypto_type tx_type state_type state_type bytes_tuple ) Bool)
(declare-fun |block_8_function_f__46_47_0| ( Int Int abi_type crypto_type tx_type state_type state_type bytes_tuple ) Bool)
(declare-fun |interface_0_C_47_0| ( Int abi_type crypto_type state_type ) Bool)
(declare-fun |block_11_function_f__46_47_0| ( Int Int abi_type crypto_type tx_type state_type state_type bytes_tuple ) Bool)
(declare-fun |block_9_function_f__46_47_0| ( Int Int abi_type crypto_type tx_type state_type state_type bytes_tuple ) Bool)
(declare-fun |block_10_function_f__46_47_0| ( Int Int abi_type crypto_type tx_type state_type state_type bytes_tuple ) Bool)
(declare-fun |block_13_function_f__46_47_0| ( Int Int abi_type crypto_type tx_type state_type state_type bytes_tuple ) Bool)
(declare-fun |contract_initializer_entry_15_C_47_0| ( Int Int abi_type crypto_type tx_type state_type state_type ) Bool)
(declare-fun |implicit_constructor_entry_17_C_47_0| ( Int Int abi_type crypto_type tx_type state_type state_type ) Bool)
(declare-fun |summary_3_function_f__46_47_0| ( Int Int abi_type crypto_type tx_type state_type state_type ) Bool)
(declare-fun |block_6_f_45_47_0| ( Int Int abi_type crypto_type tx_type state_type state_type bytes_tuple ) Bool)

(assert
  (forall ( (A abi_type) (B bytes_tuple) (C crypto_type) (D Int) (E state_type) (F state_type) (G Int) (H tx_type) ) 
    (=>
      (and
        true
      )
      (block_5_function_f__46_47_0 D G A C H E F B)
    )
  )
)
(assert
  (forall ( (A abi_type) (B bytes_tuple) (C crypto_type) (D Int) (E state_type) (F state_type) (G Int) (H tx_type) ) 
    (=>
      (and
        (block_5_function_f__46_47_0 D G A C H E F B)
        (and (= D 0) (= F E))
      )
      (block_6_f_45_47_0 D G A C H E F B)
    )
  )
)
(assert
  (forall ( (A abi_type) (B bytes_tuple) (C bytes_tuple) (D crypto_type) (E Int) (F Int) (G bytes_tuple) (H Int) (I Int) (J Bool) (K bytes_tuple) (L bytes_tuple) (M state_type) (N state_type) (O Int) (P tx_type) ) 
    (=>
      (and
        (block_6_f_45_47_0 E O A D P M N B)
        (and (= B (bytes_tuple ((as const (Array Int Int)) 0) 0))
     (= G C)
     (= C L)
     (= J (= H I))
     (= (select (bytes_tuple_accessor_array K) 1) 255)
     (= (select (bytes_tuple_accessor_array K) 0) 255)
     (= (bytes_tuple_accessor_length K) 2)
     (= I 2)
     (= H (bytes_tuple_accessor_length G))
     (= F 1)
     (>= H 0)
     (<= H
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (not J)
     (= L K))
      )
      (block_8_function_f__46_47_0 F O A D P M N C)
    )
  )
)
(assert
  (forall ( (A abi_type) (B bytes_tuple) (C crypto_type) (D Int) (E state_type) (F state_type) (G Int) (H tx_type) ) 
    (=>
      (and
        (block_8_function_f__46_47_0 D G A C H E F B)
        true
      )
      (summary_3_function_f__46_47_0 D G A C H E F)
    )
  )
)
(assert
  (forall ( (A abi_type) (B bytes_tuple) (C crypto_type) (D Int) (E state_type) (F state_type) (G Int) (H tx_type) ) 
    (=>
      (and
        (block_9_function_f__46_47_0 D G A C H E F B)
        true
      )
      (summary_3_function_f__46_47_0 D G A C H E F)
    )
  )
)
(assert
  (forall ( (A abi_type) (B bytes_tuple) (C crypto_type) (D Int) (E state_type) (F state_type) (G Int) (H tx_type) ) 
    (=>
      (and
        (block_10_function_f__46_47_0 D G A C H E F B)
        true
      )
      (summary_3_function_f__46_47_0 D G A C H E F)
    )
  )
)
(assert
  (forall ( (A abi_type) (B bytes_tuple) (C crypto_type) (D Int) (E state_type) (F state_type) (G Int) (H tx_type) ) 
    (=>
      (and
        (block_11_function_f__46_47_0 D G A C H E F B)
        true
      )
      (summary_3_function_f__46_47_0 D G A C H E F)
    )
  )
)
(assert
  (forall ( (A abi_type) (B bytes_tuple) (C crypto_type) (D Int) (E state_type) (F state_type) (G Int) (H tx_type) ) 
    (=>
      (and
        (block_12_function_f__46_47_0 D G A C H E F B)
        true
      )
      (summary_3_function_f__46_47_0 D G A C H E F)
    )
  )
)
(assert
  (forall ( (A abi_type) (B bytes_tuple) (C crypto_type) (D Int) (E state_type) (F state_type) (G Int) (H tx_type) ) 
    (=>
      (and
        (block_7_return_function_f__46_47_0 D G A C H E F B)
        true
      )
      (summary_3_function_f__46_47_0 D G A C H E F)
    )
  )
)
(assert
  (forall ( (A abi_type) (B bytes_tuple) (C bytes_tuple) (D crypto_type) (E Int) (F Int) (G Int) (H bytes_tuple) (I Int) (J Int) (K Bool) (L bytes_tuple) (M Int) (N bytes_tuple) (O bytes_tuple) (P state_type) (Q state_type) (R Int) (S tx_type) ) 
    (=>
      (and
        (block_6_f_45_47_0 E R A D S P Q B)
        (and (= B (bytes_tuple ((as const (Array Int Int)) 0) 0))
     (= L C)
     (= H C)
     (= C O)
     (= K (= I J))
     (= (select (bytes_tuple_accessor_array N) 1) 255)
     (= (select (bytes_tuple_accessor_array N) 0) 255)
     (= (bytes_tuple_accessor_length N) 2)
     (= J 2)
     (= I (bytes_tuple_accessor_length H))
     (= G 2)
     (= F E)
     (= M 0)
     (>= I 0)
     (<= I
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (or (not (<= 0 M)) (>= M (bytes_tuple_accessor_length L)))
     (= O N))
      )
      (block_9_function_f__46_47_0 G R A D S P Q C)
    )
  )
)
(assert
  (forall ( (A abi_type) (B bytes_tuple) (C bytes_tuple) (D crypto_type) (E Int) (F Int) (G Int) (H Int) (I bytes_tuple) (J Int) (K Int) (L Bool) (M bytes_tuple) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Bool) (T bytes_tuple) (U bytes_tuple) (V state_type) (W state_type) (X Int) (Y tx_type) ) 
    (=>
      (and
        (block_6_f_45_47_0 E X A D Y V W B)
        (and (= U T)
     (= M C)
     (= C U)
     (= I C)
     (= L (= J K))
     (= S (= O R))
     (= (select (bytes_tuple_accessor_array T) 1) 255)
     (= (select (bytes_tuple_accessor_array T) 0) 255)
     (= (bytes_tuple_accessor_length T) 2)
     (= R Q)
     (= G F)
     (= H 3)
     (= F E)
     (= Q P)
     (= N 0)
     (= K 2)
     (= J (bytes_tuple_accessor_length I))
     (= P 255)
     (= O (select (bytes_tuple_accessor_array C) N))
     (>= R 0)
     (>= Q 0)
     (>= J 0)
     (>= O 0)
     (<= R 255)
     (<= Q 255)
     (<= J
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= O 255)
     (not S)
     (= B (bytes_tuple ((as const (Array Int Int)) 0) 0)))
      )
      (block_10_function_f__46_47_0 H X A D Y V W C)
    )
  )
)
(assert
  (forall ( (A abi_type) (B bytes_tuple) (C bytes_tuple) (D crypto_type) (E Int) (F Int) (G Int) (H Int) (I Int) (J bytes_tuple) (K Int) (L Int) (M Bool) (N bytes_tuple) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Bool) (U bytes_tuple) (V Int) (W bytes_tuple) (X bytes_tuple) (Y state_type) (Z state_type) (A1 Int) (B1 tx_type) ) 
    (=>
      (and
        (block_6_f_45_47_0 E A1 A D B1 Y Z B)
        (and (= X W)
     (= N C)
     (= C X)
     (= J C)
     (= U C)
     (= M (= K L))
     (= T (= P S))
     (= (select (bytes_tuple_accessor_array W) 1) 255)
     (= (select (bytes_tuple_accessor_array W) 0) 255)
     (= (bytes_tuple_accessor_length W) 2)
     (= K (bytes_tuple_accessor_length J))
     (= I 4)
     (= H G)
     (= G F)
     (= F E)
     (= Q 255)
     (= L 2)
     (= S R)
     (= R Q)
     (= P (select (bytes_tuple_accessor_array C) O))
     (= O 0)
     (= V 1)
     (>= K 0)
     (>= S 0)
     (>= R 0)
     (>= P 0)
     (<= K
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= S 255)
     (<= R 255)
     (<= P 255)
     (or (not (<= 0 V)) (>= V (bytes_tuple_accessor_length U)))
     (= B (bytes_tuple ((as const (Array Int Int)) 0) 0)))
      )
      (block_11_function_f__46_47_0 I A1 A D B1 Y Z C)
    )
  )
)
(assert
  (forall ( (A abi_type) (B bytes_tuple) (C bytes_tuple) (D crypto_type) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K bytes_tuple) (L Int) (M Int) (N Bool) (O bytes_tuple) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Bool) (V bytes_tuple) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Bool) (C1 bytes_tuple) (D1 bytes_tuple) (E1 state_type) (F1 state_type) (G1 Int) (H1 tx_type) ) 
    (=>
      (and
        (block_6_f_45_47_0 E G1 A D H1 E1 F1 B)
        (and (= C D1)
     (= K C)
     (= D1 C1)
     (= V C)
     (= O C)
     (= N (= L M))
     (= U (= Q T))
     (= B1 (= X A1))
     (= (select (bytes_tuple_accessor_array C1) 1) 255)
     (= (select (bytes_tuple_accessor_array C1) 0) 255)
     (= (bytes_tuple_accessor_length C1) 2)
     (= A1 Z)
     (= H G)
     (= G F)
     (= F E)
     (= P 0)
     (= J 5)
     (= I H)
     (= Q (select (bytes_tuple_accessor_array C) P))
     (= M 2)
     (= L (bytes_tuple_accessor_length K))
     (= Z Y)
     (= W 1)
     (= T S)
     (= S R)
     (= R 255)
     (= Y 100)
     (= X (select (bytes_tuple_accessor_array C) W))
     (>= A1 0)
     (>= Q 0)
     (>= L 0)
     (>= Z 0)
     (>= T 0)
     (>= S 0)
     (>= X 0)
     (<= A1 255)
     (<= Q 255)
     (<= L
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= Z 255)
     (<= T 255)
     (<= S 255)
     (<= X 255)
     (not B1)
     (= B (bytes_tuple ((as const (Array Int Int)) 0) 0)))
      )
      (block_12_function_f__46_47_0 J G1 A D H1 E1 F1 C)
    )
  )
)
(assert
  (forall ( (A abi_type) (B bytes_tuple) (C bytes_tuple) (D crypto_type) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K bytes_tuple) (L Int) (M Int) (N Bool) (O bytes_tuple) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Bool) (V bytes_tuple) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Bool) (C1 bytes_tuple) (D1 bytes_tuple) (E1 state_type) (F1 state_type) (G1 Int) (H1 tx_type) ) 
    (=>
      (and
        (block_6_f_45_47_0 E G1 A D H1 E1 F1 B)
        (and (= C D1)
     (= K C)
     (= D1 C1)
     (= V C)
     (= O C)
     (= N (= L M))
     (= U (= Q T))
     (= B1 (= X A1))
     (= (select (bytes_tuple_accessor_array C1) 1) 255)
     (= (select (bytes_tuple_accessor_array C1) 0) 255)
     (= (bytes_tuple_accessor_length C1) 2)
     (= A1 Z)
     (= H G)
     (= G F)
     (= F E)
     (= P 0)
     (= J I)
     (= I H)
     (= Q (select (bytes_tuple_accessor_array C) P))
     (= M 2)
     (= L (bytes_tuple_accessor_length K))
     (= Z Y)
     (= W 1)
     (= T S)
     (= S R)
     (= R 255)
     (= Y 100)
     (= X (select (bytes_tuple_accessor_array C) W))
     (>= A1 0)
     (>= Q 0)
     (>= L 0)
     (>= Z 0)
     (>= T 0)
     (>= S 0)
     (>= X 0)
     (<= A1 255)
     (<= Q 255)
     (<= L
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= Z 255)
     (<= T 255)
     (<= S 255)
     (<= X 255)
     (= B (bytes_tuple ((as const (Array Int Int)) 0) 0)))
      )
      (block_7_return_function_f__46_47_0 J G1 A D H1 E1 F1 C)
    )
  )
)
(assert
  (forall ( (A abi_type) (B bytes_tuple) (C crypto_type) (D Int) (E state_type) (F state_type) (G Int) (H tx_type) ) 
    (=>
      (and
        true
      )
      (block_13_function_f__46_47_0 D G A C H E F B)
    )
  )
)
(assert
  (forall ( (A abi_type) (B bytes_tuple) (C crypto_type) (D Int) (E Int) (F Int) (G state_type) (H state_type) (I state_type) (J state_type) (K Int) (L tx_type) ) 
    (=>
      (and
        (block_13_function_f__46_47_0 D K A C L G H B)
        (summary_3_function_f__46_47_0 E K A C L I J)
        (let ((a!1 (= (select (bytes_tuple_accessor_array (msg.data L)) 3) 240))
      (a!2 (= (select (bytes_tuple_accessor_array (msg.data L)) 1) 18))
      (a!3 (= (select (bytes_tuple_accessor_array (msg.data L)) 2) 31))
      (a!4 (= (select (bytes_tuple_accessor_array (msg.data L)) 0) 38))
      (a!5 (>= (+ (select (balances H) K) F) 0))
      (a!6 (<= (+ (select (balances H) K) F)
               115792089237316195423570985008687907853269984665640564039457584007913129639935))
      (a!7 (store (balances H) K (+ (select (balances H) K) F))))
  (and (= H G)
       a!1
       a!2
       a!3
       a!4
       (= (msg.value L) 0)
       (= (msg.sig L) 638722032)
       (= D 0)
       (>= (tx.origin L) 0)
       (>= (tx.gasprice L) 0)
       (>= (msg.value L) 0)
       (>= (msg.sender L) 0)
       (>= (block.timestamp L) 0)
       (>= (block.number L) 0)
       (>= (block.gaslimit L) 0)
       (>= (block.difficulty L) 0)
       (>= (block.coinbase L) 0)
       (>= (block.chainid L) 0)
       (>= (block.basefee L) 0)
       (>= (bytes_tuple_accessor_length (msg.data L)) 4)
       a!5
       (>= F (msg.value L))
       (<= (tx.origin L) 1461501637330902918203684832716283019655932542975)
       (<= (tx.gasprice L)
           115792089237316195423570985008687907853269984665640564039457584007913129639935)
       (<= (msg.value L)
           115792089237316195423570985008687907853269984665640564039457584007913129639935)
       (<= (msg.sender L) 1461501637330902918203684832716283019655932542975)
       (<= (block.timestamp L)
           115792089237316195423570985008687907853269984665640564039457584007913129639935)
       (<= (block.number L)
           115792089237316195423570985008687907853269984665640564039457584007913129639935)
       (<= (block.gaslimit L)
           115792089237316195423570985008687907853269984665640564039457584007913129639935)
       (<= (block.difficulty L)
           115792089237316195423570985008687907853269984665640564039457584007913129639935)
       (<= (block.coinbase L) 1461501637330902918203684832716283019655932542975)
       (<= (block.chainid L)
           115792089237316195423570985008687907853269984665640564039457584007913129639935)
       (<= (block.basefee L)
           115792089237316195423570985008687907853269984665640564039457584007913129639935)
       a!6
       (= I (state_type a!7))))
      )
      (summary_4_function_f__46_47_0 E K A C L G J)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D state_type) (E state_type) (F Int) (G tx_type) ) 
    (=>
      (and
        (summary_4_function_f__46_47_0 C F A B G D E)
        (interface_0_C_47_0 F A B D)
        (= C 0)
      )
      (interface_0_C_47_0 F A B E)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D state_type) (E state_type) (F Int) (G tx_type) ) 
    (=>
      (and
        (summary_constructor_2_C_47_0 C F A B G D E)
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
      (interface_0_C_47_0 F A B E)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D state_type) (E state_type) (F Int) (G tx_type) ) 
    (=>
      (and
        (and (= C 0) (= E D))
      )
      (contract_initializer_entry_15_C_47_0 C F A B G D E)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D state_type) (E state_type) (F Int) (G tx_type) ) 
    (=>
      (and
        (contract_initializer_entry_15_C_47_0 C F A B G D E)
        true
      )
      (contract_initializer_after_init_16_C_47_0 C F A B G D E)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D state_type) (E state_type) (F Int) (G tx_type) ) 
    (=>
      (and
        (contract_initializer_after_init_16_C_47_0 C F A B G D E)
        true
      )
      (contract_initializer_14_C_47_0 C F A B G D E)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D state_type) (E state_type) (F Int) (G tx_type) ) 
    (=>
      (and
        (and (= C 0) (>= (select (balances E) F) (msg.value G)) (= E D))
      )
      (implicit_constructor_entry_17_C_47_0 C F A B G D E)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D Int) (E state_type) (F state_type) (G state_type) (H Int) (I tx_type) ) 
    (=>
      (and
        (implicit_constructor_entry_17_C_47_0 C H A B I E F)
        (contract_initializer_14_C_47_0 D H A B I F G)
        (not (<= D 0))
      )
      (summary_constructor_2_C_47_0 D H A B I E G)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D Int) (E state_type) (F state_type) (G state_type) (H Int) (I tx_type) ) 
    (=>
      (and
        (contract_initializer_14_C_47_0 D H A B I F G)
        (implicit_constructor_entry_17_C_47_0 C H A B I E F)
        (= D 0)
      )
      (summary_constructor_2_C_47_0 D H A B I E G)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D state_type) (E state_type) (F Int) (G tx_type) ) 
    (=>
      (and
        (summary_4_function_f__46_47_0 C F A B G D E)
        (interface_0_C_47_0 F A B D)
        (= C 3)
      )
      error_target_9_0
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        error_target_9_0
        true
      )
      false
    )
  )
)

(check-sat)
(exit)

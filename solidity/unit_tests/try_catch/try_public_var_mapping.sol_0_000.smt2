(set-logic HORN)

(declare-datatypes ((|uint_array_tuple| 0)) (((|uint_array_tuple|  (|uint_array_tuple_accessor_array| (Array Int Int)) (|uint_array_tuple_accessor_length| Int)))))
(declare-datatypes ((|mapping(uint256 => uint256[])_tuple| 0)) (((|mapping(uint256 => uint256[])_tuple|  (|mapping(uint256 => uint256[])_tuple_accessor_array| (Array Int uint_array_tuple)) (|mapping(uint256 => uint256[])_tuple_accessor_length| Int)))))
(declare-datatypes ((|state_type| 0)) (((|state_type|  (|balances| (Array Int Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type| ))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple|  (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type|  (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type|  (|ecrecover| (Array ecrecover_input_type Int)) (|keccak256| (Array bytes_tuple Int)) (|ripemd160| (Array bytes_tuple Int)) (|sha256| (Array bytes_tuple Int))))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type|  (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| bytes_tuple) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))

(declare-fun |contract_initializer_24_C_77_0| ( Int Int abi_type crypto_type tx_type state_type |mapping(uint256 => uint256[])_tuple| state_type |mapping(uint256 => uint256[])_tuple| ) Bool)
(declare-fun |block_23_constructor_29_77_0| ( Int Int abi_type crypto_type tx_type state_type |mapping(uint256 => uint256[])_tuple| state_type |mapping(uint256 => uint256[])_tuple| ) Bool)
(declare-fun |summary_3_constructor_29_77_0| ( Int Int abi_type crypto_type tx_type state_type |mapping(uint256 => uint256[])_tuple| state_type |mapping(uint256 => uint256[])_tuple| ) Bool)
(declare-fun |block_21__28_77_0| ( Int Int abi_type crypto_type tx_type state_type |mapping(uint256 => uint256[])_tuple| state_type |mapping(uint256 => uint256[])_tuple| ) Bool)
(declare-fun |block_22_return_constructor_29_77_0| ( Int Int abi_type crypto_type tx_type state_type |mapping(uint256 => uint256[])_tuple| state_type |mapping(uint256 => uint256[])_tuple| ) Bool)
(declare-fun |contract_initializer_entry_25_C_77_0| ( Int Int abi_type crypto_type tx_type state_type |mapping(uint256 => uint256[])_tuple| state_type |mapping(uint256 => uint256[])_tuple| ) Bool)
(declare-fun |block_20_constructor_29_77_0| ( Int Int abi_type crypto_type tx_type state_type |mapping(uint256 => uint256[])_tuple| state_type |mapping(uint256 => uint256[])_tuple| ) Bool)
(declare-fun |error_target_15_0| ( ) Bool)
(declare-fun |implicit_constructor_entry_27_C_77_0| ( Int Int abi_type crypto_type tx_type state_type |mapping(uint256 => uint256[])_tuple| state_type |mapping(uint256 => uint256[])_tuple| ) Bool)
(declare-fun |contract_initializer_after_init_26_C_77_0| ( Int Int abi_type crypto_type tx_type state_type |mapping(uint256 => uint256[])_tuple| state_type |mapping(uint256 => uint256[])_tuple| ) Bool)
(declare-fun |summary_constructor_2_C_77_0| ( Int Int abi_type crypto_type tx_type state_type |mapping(uint256 => uint256[])_tuple| state_type |mapping(uint256 => uint256[])_tuple| ) Bool)

(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D |mapping(uint256 => uint256[])_tuple|) (E |mapping(uint256 => uint256[])_tuple|) (F state_type) (G state_type) (H Int) (I tx_type) ) 
    (=>
      (and
        true
      )
      (block_20_constructor_29_77_0 C H A B I F D G E)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D |mapping(uint256 => uint256[])_tuple|) (E |mapping(uint256 => uint256[])_tuple|) (F state_type) (G state_type) (H Int) (I tx_type) ) 
    (=>
      (and
        (block_20_constructor_29_77_0 C H A B I F D G E)
        (and (= G F) (= C 0) (= E D))
      )
      (block_21__28_77_0 C H A B I F D G E)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D Int) (E uint_array_tuple) (F uint_array_tuple) (G uint_array_tuple) (H Int) (I |mapping(uint256 => uint256[])_tuple|) (J |mapping(uint256 => uint256[])_tuple|) (K |mapping(uint256 => uint256[])_tuple|) (L Int) (M uint_array_tuple) (N uint_array_tuple) (O uint_array_tuple) (P Int) (Q |mapping(uint256 => uint256[])_tuple|) (R Int) (S Int) (T uint_array_tuple) (U Int) (V |mapping(uint256 => uint256[])_tuple|) (W |mapping(uint256 => uint256[])_tuple|) (X |mapping(uint256 => uint256[])_tuple|) (Y Int) (Z |mapping(uint256 => uint256[])_tuple|) (A1 |mapping(uint256 => uint256[])_tuple|) (B1 |mapping(uint256 => uint256[])_tuple|) (C1 |mapping(uint256 => uint256[])_tuple|) (D1 state_type) (E1 state_type) (F1 Int) (G1 tx_type) ) 
    (=>
      (and
        (block_21__28_77_0 C F1 A B G1 D1 Z E1 A1)
        (let ((a!1 (= C1
              (|mapping(uint256 => uint256[])_tuple|
                (store (|mapping(uint256 => uint256[])_tuple_accessor_array| J)
                       L
                       N)
                (|mapping(uint256 => uint256[])_tuple_accessor_length| J))))
      (a!2 (= B1
              (|mapping(uint256 => uint256[])_tuple|
                (store (|mapping(uint256 => uint256[])_tuple_accessor_array| W)
                       Y
                       F)
                (|mapping(uint256 => uint256[])_tuple_accessor_length| W)))))
  (and (= (uint_array_tuple_accessor_array N)
          (store (uint_array_tuple_accessor_array M)
                 (uint_array_tuple_accessor_length M)
                 0))
       (= E
          (select (|mapping(uint256 => uint256[])_tuple_accessor_array| A1) Y))
       (= G (select (|mapping(uint256 => uint256[])_tuple_accessor_array| W) Y))
       (= T
          (select (|mapping(uint256 => uint256[])_tuple_accessor_array| C1) R))
       (= O (select (|mapping(uint256 => uint256[])_tuple_accessor_array| J) L))
       (= M
          (select (|mapping(uint256 => uint256[])_tuple_accessor_array| B1) L))
       (= I B1)
       (= K C1)
       a!1
       (= Q C1)
       (= V A1)
       (= J B1)
       (= W A1)
       (= X B1)
       a!2
       (= (uint_array_tuple_accessor_length F)
          (+ 1 (uint_array_tuple_accessor_length E)))
       (= (uint_array_tuple_accessor_length N)
          (+ 1 (uint_array_tuple_accessor_length M)))
       (= R 0)
       (= P 0)
       (= D 8)
       (= H 0)
       (= L 0)
       (= U 42)
       (= S 1)
       (= Y 0)
       (>= (uint_array_tuple_accessor_length E) 0)
       (>= (uint_array_tuple_accessor_length T) 0)
       (>= (uint_array_tuple_accessor_length M) 0)
       (>= P 0)
       (>= H 0)
       (not (<= 115792089237316195423570985008687907853269984665640564039457584007913129639933
                (uint_array_tuple_accessor_length E)))
       (not (<= 115792089237316195423570985008687907853269984665640564039457584007913129639933
                (uint_array_tuple_accessor_length M)))
       (<= P
           115792089237316195423570985008687907853269984665640564039457584007913129639935)
       (<= H
           115792089237316195423570985008687907853269984665640564039457584007913129639935)
       (or (not (<= 0 S)) (>= S (uint_array_tuple_accessor_length T)))
       (= (uint_array_tuple_accessor_array F)
          (store (uint_array_tuple_accessor_array E)
                 (uint_array_tuple_accessor_length E)
                 0))))
      )
      (block_23_constructor_29_77_0 D F1 A B G1 D1 Z E1 C1)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D |mapping(uint256 => uint256[])_tuple|) (E |mapping(uint256 => uint256[])_tuple|) (F state_type) (G state_type) (H Int) (I tx_type) ) 
    (=>
      (and
        (block_23_constructor_29_77_0 C H A B I F D G E)
        true
      )
      (summary_3_constructor_29_77_0 C H A B I F D G E)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D |mapping(uint256 => uint256[])_tuple|) (E |mapping(uint256 => uint256[])_tuple|) (F state_type) (G state_type) (H Int) (I tx_type) ) 
    (=>
      (and
        (block_22_return_constructor_29_77_0 C H A B I F D G E)
        true
      )
      (summary_3_constructor_29_77_0 C H A B I F D G E)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D Int) (E uint_array_tuple) (F uint_array_tuple) (G uint_array_tuple) (H Int) (I |mapping(uint256 => uint256[])_tuple|) (J |mapping(uint256 => uint256[])_tuple|) (K |mapping(uint256 => uint256[])_tuple|) (L Int) (M uint_array_tuple) (N uint_array_tuple) (O uint_array_tuple) (P Int) (Q |mapping(uint256 => uint256[])_tuple|) (R |mapping(uint256 => uint256[])_tuple|) (S |mapping(uint256 => uint256[])_tuple|) (T Int) (U Int) (V uint_array_tuple) (W uint_array_tuple) (X Int) (Y Int) (Z Int) (A1 Int) (B1 |mapping(uint256 => uint256[])_tuple|) (C1 |mapping(uint256 => uint256[])_tuple|) (D1 |mapping(uint256 => uint256[])_tuple|) (E1 Int) (F1 |mapping(uint256 => uint256[])_tuple|) (G1 |mapping(uint256 => uint256[])_tuple|) (H1 |mapping(uint256 => uint256[])_tuple|) (I1 |mapping(uint256 => uint256[])_tuple|) (J1 |mapping(uint256 => uint256[])_tuple|) (K1 state_type) (L1 state_type) (M1 Int) (N1 tx_type) ) 
    (=>
      (and
        (block_21__28_77_0 C M1 A B N1 K1 F1 L1 G1)
        (let ((a!1 (store (|mapping(uint256 => uint256[])_tuple_accessor_array| R)
                  T
                  (uint_array_tuple (store (uint_array_tuple_accessor_array V)
                                           U
                                           A1)
                                    (uint_array_tuple_accessor_length V))))
      (a!2 (= I1
              (|mapping(uint256 => uint256[])_tuple|
                (store (|mapping(uint256 => uint256[])_tuple_accessor_array| J)
                       L
                       N)
                (|mapping(uint256 => uint256[])_tuple_accessor_length| J))))
      (a!3 (= H1
              (|mapping(uint256 => uint256[])_tuple|
                (store (|mapping(uint256 => uint256[])_tuple_accessor_array| C1)
                       E1
                       F)
                (|mapping(uint256 => uint256[])_tuple_accessor_length| C1)))))
  (and (= (uint_array_tuple_accessor_array N)
          (store (uint_array_tuple_accessor_array M)
                 (uint_array_tuple_accessor_length M)
                 0))
       (= E
          (select (|mapping(uint256 => uint256[])_tuple_accessor_array| G1) E1))
       (= G
          (select (|mapping(uint256 => uint256[])_tuple_accessor_array| C1) E1))
       (= O (select (|mapping(uint256 => uint256[])_tuple_accessor_array| J) L))
       (= W (select (|mapping(uint256 => uint256[])_tuple_accessor_array| R) T))
       (= M
          (select (|mapping(uint256 => uint256[])_tuple_accessor_array| H1) L))
       (= V
          (select (|mapping(uint256 => uint256[])_tuple_accessor_array| I1) T))
       (= I H1)
       (= J H1)
       (= K I1)
       (= S J1)
       (= R I1)
       (= J1
          (|mapping(uint256 => uint256[])_tuple|
            a!1
            (|mapping(uint256 => uint256[])_tuple_accessor_length| R)))
       (= B1 G1)
       (= C1 G1)
       (= Q I1)
       (= D1 H1)
       a!2
       a!3
       (= (uint_array_tuple_accessor_length F)
          (+ 1 (uint_array_tuple_accessor_length E)))
       (= (uint_array_tuple_accessor_length N)
          (+ 1 (uint_array_tuple_accessor_length M)))
       (= L 0)
       (= Y (select (uint_array_tuple_accessor_array V) U))
       (= T 0)
       (= U 1)
       (= D C)
       (= H 0)
       (= P 0)
       (= A1 Z)
       (= X (select (uint_array_tuple_accessor_array V) U))
       (= Z 42)
       (= E1 0)
       (>= (uint_array_tuple_accessor_length E) 0)
       (>= (uint_array_tuple_accessor_length M) 0)
       (>= (uint_array_tuple_accessor_length V) 0)
       (>= Y 0)
       (>= H 0)
       (>= P 0)
       (>= A1 0)
       (>= X 0)
       (not (<= 115792089237316195423570985008687907853269984665640564039457584007913129639933
                (uint_array_tuple_accessor_length E)))
       (not (<= 115792089237316195423570985008687907853269984665640564039457584007913129639933
                (uint_array_tuple_accessor_length M)))
       (<= Y
           115792089237316195423570985008687907853269984665640564039457584007913129639935)
       (<= H
           115792089237316195423570985008687907853269984665640564039457584007913129639935)
       (<= P
           115792089237316195423570985008687907853269984665640564039457584007913129639935)
       (<= A1
           115792089237316195423570985008687907853269984665640564039457584007913129639935)
       (<= X
           115792089237316195423570985008687907853269984665640564039457584007913129639935)
       (= (uint_array_tuple_accessor_array F)
          (store (uint_array_tuple_accessor_array E)
                 (uint_array_tuple_accessor_length E)
                 0))))
      )
      (block_22_return_constructor_29_77_0 D M1 A B N1 K1 F1 L1 J1)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D |mapping(uint256 => uint256[])_tuple|) (E |mapping(uint256 => uint256[])_tuple|) (F state_type) (G state_type) (H Int) (I tx_type) ) 
    (=>
      (and
        (and (= G F) (= C 0) (= E D))
      )
      (contract_initializer_entry_25_C_77_0 C H A B I F D G E)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D |mapping(uint256 => uint256[])_tuple|) (E |mapping(uint256 => uint256[])_tuple|) (F state_type) (G state_type) (H Int) (I tx_type) ) 
    (=>
      (and
        (contract_initializer_entry_25_C_77_0 C H A B I F D G E)
        true
      )
      (contract_initializer_after_init_26_C_77_0 C H A B I F D G E)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D Int) (E |mapping(uint256 => uint256[])_tuple|) (F |mapping(uint256 => uint256[])_tuple|) (G |mapping(uint256 => uint256[])_tuple|) (H state_type) (I state_type) (J state_type) (K Int) (L tx_type) ) 
    (=>
      (and
        (contract_initializer_after_init_26_C_77_0 C K A B L H E I F)
        (summary_3_constructor_29_77_0 D K A B L I F J G)
        (not (<= D 0))
      )
      (contract_initializer_24_C_77_0 D K A B L H E J G)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D Int) (E |mapping(uint256 => uint256[])_tuple|) (F |mapping(uint256 => uint256[])_tuple|) (G |mapping(uint256 => uint256[])_tuple|) (H state_type) (I state_type) (J state_type) (K Int) (L tx_type) ) 
    (=>
      (and
        (summary_3_constructor_29_77_0 D K A B L I F J G)
        (contract_initializer_after_init_26_C_77_0 C K A B L H E I F)
        (= D 0)
      )
      (contract_initializer_24_C_77_0 D K A B L H E J G)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D |mapping(uint256 => uint256[])_tuple|) (E |mapping(uint256 => uint256[])_tuple|) (F state_type) (G state_type) (H Int) (I tx_type) ) 
    (=>
      (and
        (let ((a!1 (|mapping(uint256 => uint256[])_tuple|
             ((as const (Array Int uint_array_tuple))
               (uint_array_tuple ((as const (Array Int Int)) 0) 0))
             0)))
  (and (= E D)
       (= G F)
       (= C 0)
       (>= (select (balances G) H) (msg.value I))
       (= E a!1)))
      )
      (implicit_constructor_entry_27_C_77_0 C H A B I F D G E)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D Int) (E |mapping(uint256 => uint256[])_tuple|) (F |mapping(uint256 => uint256[])_tuple|) (G |mapping(uint256 => uint256[])_tuple|) (H state_type) (I state_type) (J state_type) (K Int) (L tx_type) ) 
    (=>
      (and
        (implicit_constructor_entry_27_C_77_0 C K A B L H E I F)
        (contract_initializer_24_C_77_0 D K A B L I F J G)
        (not (<= D 0))
      )
      (summary_constructor_2_C_77_0 D K A B L H E J G)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D Int) (E |mapping(uint256 => uint256[])_tuple|) (F |mapping(uint256 => uint256[])_tuple|) (G |mapping(uint256 => uint256[])_tuple|) (H state_type) (I state_type) (J state_type) (K Int) (L tx_type) ) 
    (=>
      (and
        (contract_initializer_24_C_77_0 D K A B L I F J G)
        (implicit_constructor_entry_27_C_77_0 C K A B L H E I F)
        (= D 0)
      )
      (summary_constructor_2_C_77_0 D K A B L H E J G)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D |mapping(uint256 => uint256[])_tuple|) (E |mapping(uint256 => uint256[])_tuple|) (F state_type) (G state_type) (H Int) (I tx_type) ) 
    (=>
      (and
        (summary_constructor_2_C_77_0 C H A B I F D G E)
        (and (= C 8)
     (>= (tx.origin I) 0)
     (>= (tx.gasprice I) 0)
     (>= (msg.value I) 0)
     (>= (msg.sender I) 0)
     (>= (block.timestamp I) 0)
     (>= (block.number I) 0)
     (>= (block.gaslimit I) 0)
     (>= (block.difficulty I) 0)
     (>= (block.coinbase I) 0)
     (>= (block.chainid I) 0)
     (>= (block.basefee I) 0)
     (<= (tx.origin I) 1461501637330902918203684832716283019655932542975)
     (<= (tx.gasprice I)
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= (msg.value I)
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= (msg.sender I) 1461501637330902918203684832716283019655932542975)
     (<= (block.timestamp I)
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= (block.number I)
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= (block.gaslimit I)
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= (block.difficulty I)
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= (block.coinbase I) 1461501637330902918203684832716283019655932542975)
     (<= (block.chainid I)
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= (block.basefee I)
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (= (msg.value I) 0))
      )
      error_target_15_0
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        error_target_15_0
        true
      )
      false
    )
  )
)

(check-sat)
(exit)

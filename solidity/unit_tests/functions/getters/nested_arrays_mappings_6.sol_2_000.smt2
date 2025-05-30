(set-logic HORN)

(declare-datatypes ((|uint_array_tuple| 0)) (((|uint_array_tuple|  (|uint_array_tuple_accessor_array| (Array Int Int)) (|uint_array_tuple_accessor_length| Int)))))
(declare-datatypes ((|mapping(uint256 => uint256[])_tuple| 0)) (((|mapping(uint256 => uint256[])_tuple|  (|mapping(uint256 => uint256[])_tuple_accessor_array| (Array Int uint_array_tuple)) (|mapping(uint256 => uint256[])_tuple_accessor_length| Int)))))
(declare-datatypes ((|state_type| 0)) (((|state_type|  (|balances| (Array Int Int))))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type| ))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple|  (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type|  (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type|  (|ecrecover| (Array ecrecover_input_type Int)) (|keccak256| (Array bytes_tuple Int)) (|ripemd160| (Array bytes_tuple Int)) (|sha256| (Array bytes_tuple Int))))))
(declare-datatypes ((|mapping(uint256 => mapping(uint256 => uint256[]))_tuple| 0)) (((|mapping(uint256 => mapping(uint256 => uint256[]))_tuple|  (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple_accessor_array| (Array Int |mapping(uint256 => uint256[])_tuple|)) (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple_accessor_length| Int)))))
(declare-datatypes ((|mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple| 0)) (((|mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|  (|mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple_accessor_array| (Array Int |mapping(uint256 => mapping(uint256 => uint256[]))_tuple|)) (|mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple_accessor_length| Int)))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type|  (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| bytes_tuple) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))

(declare-fun |summary_3_constructor_65_100_0| ( Int Int abi_type crypto_type tx_type state_type |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple| state_type |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple| ) Bool)
(declare-fun |contract_initializer_17_C_100_0| ( Int Int abi_type crypto_type tx_type state_type |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple| state_type |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple| ) Bool)
(declare-fun |block_14__64_100_0| ( Int Int abi_type crypto_type tx_type state_type |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple| state_type |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple| ) Bool)
(declare-fun |block_16_constructor_65_100_0| ( Int Int abi_type crypto_type tx_type state_type |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple| state_type |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple| ) Bool)
(declare-fun |summary_constructor_2_C_100_0| ( Int Int abi_type crypto_type tx_type state_type |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple| state_type |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple| ) Bool)
(declare-fun |implicit_constructor_entry_20_C_100_0| ( Int Int abi_type crypto_type tx_type state_type |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple| state_type |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple| ) Bool)
(declare-fun |block_13_constructor_65_100_0| ( Int Int abi_type crypto_type tx_type state_type |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple| state_type |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple| ) Bool)
(declare-fun |contract_initializer_after_init_19_C_100_0| ( Int Int abi_type crypto_type tx_type state_type |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple| state_type |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple| ) Bool)
(declare-fun |contract_initializer_entry_18_C_100_0| ( Int Int abi_type crypto_type tx_type state_type |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple| state_type |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple| ) Bool)
(declare-fun |error_target_9_0| ( ) Bool)
(declare-fun |block_15_return_constructor_65_100_0| ( Int Int abi_type crypto_type tx_type state_type |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple| state_type |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple| ) Bool)

(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (E |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (F state_type) (G state_type) (H Int) (I tx_type) ) 
    (=>
      (and
        true
      )
      (block_13_constructor_65_100_0 C H A B I F D G E)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (E |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (F state_type) (G state_type) (H Int) (I tx_type) ) 
    (=>
      (and
        (block_13_constructor_65_100_0 C H A B I F D G E)
        (and (= G F) (= C 0) (= E D))
      )
      (block_14__64_100_0 C H A B I F D G E)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D Int) (E |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (F |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (G |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (H Int) (I Int) (J Int) (K |mapping(uint256 => mapping(uint256 => uint256[]))_tuple|) (L |mapping(uint256 => mapping(uint256 => uint256[]))_tuple|) (M |mapping(uint256 => uint256[])_tuple|) (N |mapping(uint256 => uint256[])_tuple|) (O uint_array_tuple) (P uint_array_tuple) (Q uint_array_tuple) (R Int) (S |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (T |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (U |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (V Int) (W Int) (X Int) (Y |mapping(uint256 => mapping(uint256 => uint256[]))_tuple|) (Z |mapping(uint256 => mapping(uint256 => uint256[]))_tuple|) (A1 |mapping(uint256 => uint256[])_tuple|) (B1 |mapping(uint256 => uint256[])_tuple|) (C1 uint_array_tuple) (D1 uint_array_tuple) (E1 uint_array_tuple) (F1 Int) (G1 |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (H1 |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (I1 |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (J1 Int) (K1 Int) (L1 Int) (M1 |mapping(uint256 => mapping(uint256 => uint256[]))_tuple|) (N1 |mapping(uint256 => mapping(uint256 => uint256[]))_tuple|) (O1 |mapping(uint256 => uint256[])_tuple|) (P1 |mapping(uint256 => uint256[])_tuple|) (Q1 uint_array_tuple) (R1 uint_array_tuple) (S1 uint_array_tuple) (T1 Int) (U1 |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (V1 |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (W1 |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (X1 Int) (Y1 Int) (Z1 Int) (A2 |mapping(uint256 => mapping(uint256 => uint256[]))_tuple|) (B2 |mapping(uint256 => mapping(uint256 => uint256[]))_tuple|) (C2 |mapping(uint256 => uint256[])_tuple|) (D2 |mapping(uint256 => uint256[])_tuple|) (E2 uint_array_tuple) (F2 uint_array_tuple) (G2 uint_array_tuple) (H2 Int) (I2 |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (J2 Int) (K2 Int) (L2 Int) (M2 Int) (N2 |mapping(uint256 => mapping(uint256 => uint256[]))_tuple|) (O2 |mapping(uint256 => uint256[])_tuple|) (P2 uint_array_tuple) (Q2 Int) (R2 |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (S2 |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (T2 |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (U2 |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (V2 |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (W2 |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (X2 state_type) (Y2 state_type) (Z2 Int) (A3 tx_type) ) 
    (=>
      (and
        (block_14__64_100_0 C Z2 A B A3 X2 R2 Y2 S2)
        (let ((a!1 (store (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple_accessor_array|
                    A2)
                  Y1
                  (|mapping(uint256 => uint256[])_tuple|
                    (store (|mapping(uint256 => uint256[])_tuple_accessor_array|
                             C2)
                           Z1
                           F2)
                    (|mapping(uint256 => uint256[])_tuple_accessor_length| C2))))
      (a!3 (store (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple_accessor_array|
                    M1)
                  K1
                  (|mapping(uint256 => uint256[])_tuple|
                    (store (|mapping(uint256 => uint256[])_tuple_accessor_array|
                             O1)
                           L1
                           R1)
                    (|mapping(uint256 => uint256[])_tuple_accessor_length| O1))))
      (a!5 (store (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple_accessor_array|
                    Y)
                  W
                  (|mapping(uint256 => uint256[])_tuple|
                    (store (|mapping(uint256 => uint256[])_tuple_accessor_array|
                             A1)
                           X
                           D1)
                    (|mapping(uint256 => uint256[])_tuple_accessor_length| A1))))
      (a!7 (store (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple_accessor_array|
                    K)
                  I
                  (|mapping(uint256 => uint256[])_tuple|
                    (store (|mapping(uint256 => uint256[])_tuple_accessor_array|
                             M)
                           J
                           P)
                    (|mapping(uint256 => uint256[])_tuple_accessor_length| M)))))
(let ((a!2 (|mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|
             (store (|mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple_accessor_array|
                      V1)
                    X1
                    (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple|
                      a!1
                      (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple_accessor_length|
                        A2)))
             (|mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple_accessor_length|
               V1)))
      (a!4 (|mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|
             (store (|mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple_accessor_array|
                      H1)
                    J1
                    (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple|
                      a!3
                      (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple_accessor_length|
                        M1)))
             (|mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple_accessor_length|
               H1)))
      (a!6 (|mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|
             (store (|mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple_accessor_array|
                      T)
                    V
                    (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple|
                      a!5
                      (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple_accessor_length|
                        Y)))
             (|mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple_accessor_length|
               T)))
      (a!8 (|mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|
             (store (|mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple_accessor_array|
                      F)
                    H
                    (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple|
                      a!7
                      (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple_accessor_length|
                        K)))
             (|mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple_accessor_length|
               F))))
  (and (= (uint_array_tuple_accessor_array R1)
          (store (uint_array_tuple_accessor_array Q1)
                 (uint_array_tuple_accessor_length Q1)
                 0))
       (= (uint_array_tuple_accessor_array F2)
          (store (uint_array_tuple_accessor_array E2)
                 (uint_array_tuple_accessor_length E2)
                 0))
       (= (uint_array_tuple_accessor_array P)
          (store (uint_array_tuple_accessor_array O)
                 (uint_array_tuple_accessor_length O)
                 0))
       (= L
          (select (|mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple_accessor_array|
                    F)
                  H))
       (= Y
          (select (|mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple_accessor_array|
                    T2)
                  V))
       (= Z
          (select (|mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple_accessor_array|
                    T)
                  V))
       (= M1
          (select (|mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple_accessor_array|
                    U2)
                  J1))
       (= N1
          (select (|mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple_accessor_array|
                    H1)
                  J1))
       (= A2
          (select (|mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple_accessor_array|
                    V2)
                  X1))
       (= B2
          (select (|mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple_accessor_array|
                    V1)
                  X1))
       (= N2
          (select (|mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple_accessor_array|
                    W2)
                  J2))
       (= K
          (select (|mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple_accessor_array|
                    S2)
                  H))
       (= A1
          (select (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple_accessor_array|
                    Y)
                  W))
       (= B1
          (select (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple_accessor_array|
                    Y)
                  W))
       (= O1
          (select (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple_accessor_array|
                    M1)
                  K1))
       (= P1
          (select (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple_accessor_array|
                    M1)
                  K1))
       (= C2
          (select (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple_accessor_array|
                    A2)
                  Y1))
       (= D2
          (select (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple_accessor_array|
                    A2)
                  Y1))
       (= O2
          (select (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple_accessor_array|
                    N2)
                  K2))
       (= N
          (select (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple_accessor_array|
                    K)
                  I))
       (= M
          (select (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple_accessor_array|
                    K)
                  I))
       (= O (select (|mapping(uint256 => uint256[])_tuple_accessor_array| M) J))
       (= C1
          (select (|mapping(uint256 => uint256[])_tuple_accessor_array| A1) X))
       (= E1
          (select (|mapping(uint256 => uint256[])_tuple_accessor_array| A1) X))
       (= Q1
          (select (|mapping(uint256 => uint256[])_tuple_accessor_array| O1) L1))
       (= S1
          (select (|mapping(uint256 => uint256[])_tuple_accessor_array| O1) L1))
       (= E2
          (select (|mapping(uint256 => uint256[])_tuple_accessor_array| C2) Z1))
       (= G2
          (select (|mapping(uint256 => uint256[])_tuple_accessor_array| C2) Z1))
       (= P2
          (select (|mapping(uint256 => uint256[])_tuple_accessor_array| O2) L2))
       (= Q (select (|mapping(uint256 => uint256[])_tuple_accessor_array| M) J))
       (= F S2)
       (= G T2)
       (= S T2)
       (= G1 U2)
       (= H1 U2)
       (= I1 V2)
       (= U1 V2)
       (= V1 V2)
       (= W1 W2)
       (= I2 W2)
       (= W2 a!2)
       (= U U2)
       (= T T2)
       (= E S2)
       (= V2 a!4)
       (= U2 a!6)
       (= T2 a!8)
       (= (uint_array_tuple_accessor_length D1)
          (+ 1 (uint_array_tuple_accessor_length C1)))
       (= (uint_array_tuple_accessor_length R1)
          (+ 1 (uint_array_tuple_accessor_length Q1)))
       (= (uint_array_tuple_accessor_length F2)
          (+ 1 (uint_array_tuple_accessor_length E2)))
       (= (uint_array_tuple_accessor_length P)
          (+ 1 (uint_array_tuple_accessor_length O)))
       (= D 5)
       (= I 1)
       (= J 2)
       (= R 0)
       (= V 0)
       (= Q2 42)
       (= L1 2)
       (= K1 1)
       (= J1 0)
       (= X 2)
       (= W 1)
       (= H 0)
       (= F1 0)
       (= L2 2)
       (= K2 1)
       (= H2 0)
       (= T1 0)
       (= M2 3)
       (= J2 0)
       (= Z1 2)
       (= Y1 1)
       (= X1 0)
       (>= (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple_accessor_length|
             Y)
           0)
       (>= (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple_accessor_length|
             M1)
           0)
       (>= (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple_accessor_length|
             A2)
           0)
       (>= (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple_accessor_length|
             N2)
           0)
       (>= (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple_accessor_length|
             K)
           0)
       (>= (|mapping(uint256 => uint256[])_tuple_accessor_length| A1) 0)
       (>= (|mapping(uint256 => uint256[])_tuple_accessor_length| O1) 0)
       (>= (|mapping(uint256 => uint256[])_tuple_accessor_length| C2) 0)
       (>= (|mapping(uint256 => uint256[])_tuple_accessor_length| O2) 0)
       (>= (|mapping(uint256 => uint256[])_tuple_accessor_length| M) 0)
       (>= (uint_array_tuple_accessor_length O) 0)
       (>= (uint_array_tuple_accessor_length C1) 0)
       (>= (uint_array_tuple_accessor_length Q1) 0)
       (>= (uint_array_tuple_accessor_length E2) 0)
       (>= (uint_array_tuple_accessor_length P2) 0)
       (>= R 0)
       (>= F1 0)
       (>= H2 0)
       (>= T1 0)
       (not (<= 115792089237316195423570985008687907853269984665640564039457584007913129639933
                (uint_array_tuple_accessor_length O)))
       (not (<= 115792089237316195423570985008687907853269984665640564039457584007913129639933
                (uint_array_tuple_accessor_length C1)))
       (not (<= 115792089237316195423570985008687907853269984665640564039457584007913129639933
                (uint_array_tuple_accessor_length Q1)))
       (not (<= 115792089237316195423570985008687907853269984665640564039457584007913129639933
                (uint_array_tuple_accessor_length E2)))
       (<= R
           115792089237316195423570985008687907853269984665640564039457584007913129639935)
       (<= F1
           115792089237316195423570985008687907853269984665640564039457584007913129639935)
       (<= H2
           115792089237316195423570985008687907853269984665640564039457584007913129639935)
       (<= T1
           115792089237316195423570985008687907853269984665640564039457584007913129639935)
       (or (not (<= 0 M2)) (>= M2 (uint_array_tuple_accessor_length P2)))
       (= (uint_array_tuple_accessor_array D1)
          (store (uint_array_tuple_accessor_array C1)
                 (uint_array_tuple_accessor_length C1)
                 0)))))
      )
      (block_16_constructor_65_100_0 D Z2 A B A3 X2 R2 Y2 W2)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (E |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (F state_type) (G state_type) (H Int) (I tx_type) ) 
    (=>
      (and
        (block_16_constructor_65_100_0 C H A B I F D G E)
        true
      )
      (summary_3_constructor_65_100_0 C H A B I F D G E)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (E |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (F state_type) (G state_type) (H Int) (I tx_type) ) 
    (=>
      (and
        (block_15_return_constructor_65_100_0 C H A B I F D G E)
        true
      )
      (summary_3_constructor_65_100_0 C H A B I F D G E)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D Int) (E |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (F |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (G |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (H Int) (I Int) (J Int) (K |mapping(uint256 => mapping(uint256 => uint256[]))_tuple|) (L |mapping(uint256 => mapping(uint256 => uint256[]))_tuple|) (M |mapping(uint256 => uint256[])_tuple|) (N |mapping(uint256 => uint256[])_tuple|) (O uint_array_tuple) (P uint_array_tuple) (Q uint_array_tuple) (R Int) (S |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (T |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (U |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (V Int) (W Int) (X Int) (Y |mapping(uint256 => mapping(uint256 => uint256[]))_tuple|) (Z |mapping(uint256 => mapping(uint256 => uint256[]))_tuple|) (A1 |mapping(uint256 => uint256[])_tuple|) (B1 |mapping(uint256 => uint256[])_tuple|) (C1 uint_array_tuple) (D1 uint_array_tuple) (E1 uint_array_tuple) (F1 Int) (G1 |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (H1 |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (I1 |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (J1 Int) (K1 Int) (L1 Int) (M1 |mapping(uint256 => mapping(uint256 => uint256[]))_tuple|) (N1 |mapping(uint256 => mapping(uint256 => uint256[]))_tuple|) (O1 |mapping(uint256 => uint256[])_tuple|) (P1 |mapping(uint256 => uint256[])_tuple|) (Q1 uint_array_tuple) (R1 uint_array_tuple) (S1 uint_array_tuple) (T1 Int) (U1 |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (V1 |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (W1 |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (X1 Int) (Y1 Int) (Z1 Int) (A2 |mapping(uint256 => mapping(uint256 => uint256[]))_tuple|) (B2 |mapping(uint256 => mapping(uint256 => uint256[]))_tuple|) (C2 |mapping(uint256 => uint256[])_tuple|) (D2 |mapping(uint256 => uint256[])_tuple|) (E2 uint_array_tuple) (F2 uint_array_tuple) (G2 uint_array_tuple) (H2 Int) (I2 |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (J2 |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (K2 |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (L2 Int) (M2 Int) (N2 Int) (O2 Int) (P2 |mapping(uint256 => mapping(uint256 => uint256[]))_tuple|) (Q2 |mapping(uint256 => mapping(uint256 => uint256[]))_tuple|) (R2 |mapping(uint256 => uint256[])_tuple|) (S2 |mapping(uint256 => uint256[])_tuple|) (T2 uint_array_tuple) (U2 uint_array_tuple) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (A3 |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (B3 |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (C3 |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (D3 |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (E3 |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (F3 |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (G3 state_type) (H3 state_type) (I3 Int) (J3 tx_type) ) 
    (=>
      (and
        (block_14__64_100_0 C I3 A B J3 G3 Z2 H3 A3)
        (let ((a!1 (store (|mapping(uint256 => uint256[])_tuple_accessor_array| R2)
                  N2
                  (uint_array_tuple (store (uint_array_tuple_accessor_array T2)
                                           O2
                                           Y2)
                                    (uint_array_tuple_accessor_length T2))))
      (a!4 (store (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple_accessor_array|
                    K)
                  I
                  (|mapping(uint256 => uint256[])_tuple|
                    (store (|mapping(uint256 => uint256[])_tuple_accessor_array|
                             M)
                           J
                           P)
                    (|mapping(uint256 => uint256[])_tuple_accessor_length| M))))
      (a!6 (store (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple_accessor_array|
                    A2)
                  Y1
                  (|mapping(uint256 => uint256[])_tuple|
                    (store (|mapping(uint256 => uint256[])_tuple_accessor_array|
                             C2)
                           Z1
                           F2)
                    (|mapping(uint256 => uint256[])_tuple_accessor_length| C2))))
      (a!8 (store (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple_accessor_array|
                    M1)
                  K1
                  (|mapping(uint256 => uint256[])_tuple|
                    (store (|mapping(uint256 => uint256[])_tuple_accessor_array|
                             O1)
                           L1
                           R1)
                    (|mapping(uint256 => uint256[])_tuple_accessor_length| O1))))
      (a!10 (store (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple_accessor_array|
                     Y)
                   W
                   (|mapping(uint256 => uint256[])_tuple|
                     (store (|mapping(uint256 => uint256[])_tuple_accessor_array|
                              A1)
                            X
                            D1)
                     (|mapping(uint256 => uint256[])_tuple_accessor_length| A1)))))
(let ((a!2 (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple|
             (store (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple_accessor_array|
                      P2)
                    M2
                    (|mapping(uint256 => uint256[])_tuple|
                      a!1
                      (|mapping(uint256 => uint256[])_tuple_accessor_length| R2)))
             (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple_accessor_length|
               P2)))
      (a!5 (|mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|
             (store (|mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple_accessor_array|
                      F)
                    H
                    (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple|
                      a!4
                      (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple_accessor_length|
                        K)))
             (|mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple_accessor_length|
               F)))
      (a!7 (|mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|
             (store (|mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple_accessor_array|
                      V1)
                    X1
                    (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple|
                      a!6
                      (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple_accessor_length|
                        A2)))
             (|mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple_accessor_length|
               V1)))
      (a!9 (|mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|
             (store (|mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple_accessor_array|
                      H1)
                    J1
                    (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple|
                      a!8
                      (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple_accessor_length|
                        M1)))
             (|mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple_accessor_length|
               H1)))
      (a!11 (|mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|
              (store (|mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple_accessor_array|
                       T)
                     V
                     (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple|
                       a!10
                       (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple_accessor_length|
                         Y)))
              (|mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple_accessor_length|
                T))))
(let ((a!3 (= F3
              (|mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|
                (store (|mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple_accessor_array|
                         J2)
                       L2
                       a!2)
                (|mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple_accessor_length|
                  J2)))))
  (and (= (uint_array_tuple_accessor_array D1)
          (store (uint_array_tuple_accessor_array C1)
                 (uint_array_tuple_accessor_length C1)
                 0))
       (= (uint_array_tuple_accessor_array F2)
          (store (uint_array_tuple_accessor_array E2)
                 (uint_array_tuple_accessor_length E2)
                 0))
       (= (uint_array_tuple_accessor_array R1)
          (store (uint_array_tuple_accessor_array Q1)
                 (uint_array_tuple_accessor_length Q1)
                 0))
       (= Y
          (select (|mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple_accessor_array|
                    B3)
                  V))
       (= Z
          (select (|mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple_accessor_array|
                    T)
                  V))
       (= M1
          (select (|mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple_accessor_array|
                    C3)
                  J1))
       (= N1
          (select (|mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple_accessor_array|
                    H1)
                  J1))
       (= A2
          (select (|mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple_accessor_array|
                    D3)
                  X1))
       (= B2
          (select (|mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple_accessor_array|
                    V1)
                  X1))
       (= Q2
          (select (|mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple_accessor_array|
                    J2)
                  L2))
       (= L
          (select (|mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple_accessor_array|
                    F)
                  H))
       (= K
          (select (|mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple_accessor_array|
                    A3)
                  H))
       (= P2
          (select (|mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple_accessor_array|
                    E3)
                  L2))
       (= M
          (select (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple_accessor_array|
                    K)
                  I))
       (= A1
          (select (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple_accessor_array|
                    Y)
                  W))
       (= B1
          (select (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple_accessor_array|
                    Y)
                  W))
       (= P1
          (select (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple_accessor_array|
                    M1)
                  K1))
       (= C2
          (select (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple_accessor_array|
                    A2)
                  Y1))
       (= D2
          (select (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple_accessor_array|
                    A2)
                  Y1))
       (= R2
          (select (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple_accessor_array|
                    P2)
                  M2))
       (= O1
          (select (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple_accessor_array|
                    M1)
                  K1))
       (= N
          (select (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple_accessor_array|
                    K)
                  I))
       (= S2
          (select (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple_accessor_array|
                    P2)
                  M2))
       (= O (select (|mapping(uint256 => uint256[])_tuple_accessor_array| M) J))
       (= C1
          (select (|mapping(uint256 => uint256[])_tuple_accessor_array| A1) X))
       (= E1
          (select (|mapping(uint256 => uint256[])_tuple_accessor_array| A1) X))
       (= S1
          (select (|mapping(uint256 => uint256[])_tuple_accessor_array| O1) L1))
       (= E2
          (select (|mapping(uint256 => uint256[])_tuple_accessor_array| C2) Z1))
       (= G2
          (select (|mapping(uint256 => uint256[])_tuple_accessor_array| C2) Z1))
       (= T2
          (select (|mapping(uint256 => uint256[])_tuple_accessor_array| R2) N2))
       (= U2
          (select (|mapping(uint256 => uint256[])_tuple_accessor_array| R2) N2))
       (= Q1
          (select (|mapping(uint256 => uint256[])_tuple_accessor_array| O1) L1))
       (= Q (select (|mapping(uint256 => uint256[])_tuple_accessor_array| M) J))
       (= G B3)
       (= S B3)
       (= T B3)
       (= G1 C3)
       (= H1 C3)
       (= I1 D3)
       (= U1 D3)
       (= V1 D3)
       (= W1 E3)
       (= I2 E3)
       (= K2 F3)
       a!3
       (= U C3)
       (= F A3)
       (= E A3)
       (= J2 E3)
       (= B3 a!5)
       (= E3 a!7)
       (= D3 a!9)
       (= C3 a!11)
       (= (uint_array_tuple_accessor_length P)
          (+ 1 (uint_array_tuple_accessor_length O)))
       (= (uint_array_tuple_accessor_length D1)
          (+ 1 (uint_array_tuple_accessor_length C1)))
       (= (uint_array_tuple_accessor_length F2)
          (+ 1 (uint_array_tuple_accessor_length E2)))
       (= (uint_array_tuple_accessor_length R1)
          (+ 1 (uint_array_tuple_accessor_length Q1)))
       (= D C)
       (= J 2)
       (= V 0)
       (= W 1)
       (= J1 0)
       (= L1 2)
       (= R 0)
       (= O2 3)
       (= T1 0)
       (= F1 0)
       (= K1 1)
       (= X 2)
       (= I 1)
       (= H 0)
       (= X1 0)
       (= Z1 2)
       (= X2 42)
       (= W2 (select (uint_array_tuple_accessor_array T2) O2))
       (= Y1 1)
       (= V2 (select (uint_array_tuple_accessor_array T2) O2))
       (= N2 2)
       (= M2 1)
       (= L2 0)
       (= H2 0)
       (= Y2 X2)
       (>= (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple_accessor_length|
             Y)
           0)
       (>= (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple_accessor_length|
             M1)
           0)
       (>= (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple_accessor_length|
             A2)
           0)
       (>= (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple_accessor_length|
             K)
           0)
       (>= (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple_accessor_length|
             P2)
           0)
       (>= (|mapping(uint256 => uint256[])_tuple_accessor_length| M) 0)
       (>= (|mapping(uint256 => uint256[])_tuple_accessor_length| A1) 0)
       (>= (|mapping(uint256 => uint256[])_tuple_accessor_length| C2) 0)
       (>= (|mapping(uint256 => uint256[])_tuple_accessor_length| R2) 0)
       (>= (|mapping(uint256 => uint256[])_tuple_accessor_length| O1) 0)
       (>= (uint_array_tuple_accessor_length O) 0)
       (>= (uint_array_tuple_accessor_length C1) 0)
       (>= (uint_array_tuple_accessor_length E2) 0)
       (>= (uint_array_tuple_accessor_length T2) 0)
       (>= (uint_array_tuple_accessor_length Q1) 0)
       (>= R 0)
       (>= T1 0)
       (>= F1 0)
       (>= W2 0)
       (>= V2 0)
       (>= H2 0)
       (>= Y2 0)
       (not (<= 115792089237316195423570985008687907853269984665640564039457584007913129639933
                (uint_array_tuple_accessor_length O)))
       (not (<= 115792089237316195423570985008687907853269984665640564039457584007913129639933
                (uint_array_tuple_accessor_length C1)))
       (not (<= 115792089237316195423570985008687907853269984665640564039457584007913129639933
                (uint_array_tuple_accessor_length E2)))
       (not (<= 115792089237316195423570985008687907853269984665640564039457584007913129639933
                (uint_array_tuple_accessor_length Q1)))
       (<= R
           115792089237316195423570985008687907853269984665640564039457584007913129639935)
       (<= T1
           115792089237316195423570985008687907853269984665640564039457584007913129639935)
       (<= F1
           115792089237316195423570985008687907853269984665640564039457584007913129639935)
       (<= W2
           115792089237316195423570985008687907853269984665640564039457584007913129639935)
       (<= V2
           115792089237316195423570985008687907853269984665640564039457584007913129639935)
       (<= H2
           115792089237316195423570985008687907853269984665640564039457584007913129639935)
       (<= Y2
           115792089237316195423570985008687907853269984665640564039457584007913129639935)
       (= (uint_array_tuple_accessor_array P)
          (store (uint_array_tuple_accessor_array O)
                 (uint_array_tuple_accessor_length O)
                 0))))))
      )
      (block_15_return_constructor_65_100_0 D I3 A B J3 G3 Z2 H3 F3)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (E |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (F state_type) (G state_type) (H Int) (I tx_type) ) 
    (=>
      (and
        (and (= G F) (= C 0) (= E D))
      )
      (contract_initializer_entry_18_C_100_0 C H A B I F D G E)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (E |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (F state_type) (G state_type) (H Int) (I tx_type) ) 
    (=>
      (and
        (contract_initializer_entry_18_C_100_0 C H A B I F D G E)
        true
      )
      (contract_initializer_after_init_19_C_100_0 C H A B I F D G E)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D Int) (E |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (F |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (G |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (H state_type) (I state_type) (J state_type) (K Int) (L tx_type) ) 
    (=>
      (and
        (contract_initializer_after_init_19_C_100_0 C K A B L H E I F)
        (summary_3_constructor_65_100_0 D K A B L I F J G)
        (not (<= D 0))
      )
      (contract_initializer_17_C_100_0 D K A B L H E J G)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D Int) (E |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (F |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (G |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (H state_type) (I state_type) (J state_type) (K Int) (L tx_type) ) 
    (=>
      (and
        (summary_3_constructor_65_100_0 D K A B L I F J G)
        (contract_initializer_after_init_19_C_100_0 C K A B L H E I F)
        (= D 0)
      )
      (contract_initializer_17_C_100_0 D K A B L H E J G)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (E |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (F state_type) (G state_type) (H Int) (I tx_type) ) 
    (=>
      (and
        (let ((a!1 (|mapping(uint256 => uint256[])_tuple|
             ((as const (Array Int uint_array_tuple))
               (uint_array_tuple ((as const (Array Int Int)) 0) 0))
             0)))
(let ((a!2 (|mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|
             ((as const
                  (Array Int
                         |mapping(uint256 => mapping(uint256 => uint256[]))_tuple|))
               (|mapping(uint256 => mapping(uint256 => uint256[]))_tuple|
                 ((as const (Array Int |mapping(uint256 => uint256[])_tuple|))
                   a!1)
                 0))
             0)))
  (and (= E D)
       (= G F)
       (= C 0)
       (>= (select (balances G) H) (msg.value I))
       (= E a!2))))
      )
      (implicit_constructor_entry_20_C_100_0 C H A B I F D G E)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D Int) (E |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (F |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (G |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (H state_type) (I state_type) (J state_type) (K Int) (L tx_type) ) 
    (=>
      (and
        (implicit_constructor_entry_20_C_100_0 C K A B L H E I F)
        (contract_initializer_17_C_100_0 D K A B L I F J G)
        (not (<= D 0))
      )
      (summary_constructor_2_C_100_0 D K A B L H E J G)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D Int) (E |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (F |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (G |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (H state_type) (I state_type) (J state_type) (K Int) (L tx_type) ) 
    (=>
      (and
        (contract_initializer_17_C_100_0 D K A B L I F J G)
        (implicit_constructor_entry_20_C_100_0 C K A B L H E I F)
        (= D 0)
      )
      (summary_constructor_2_C_100_0 D K A B L H E J G)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (E |mapping(uint256 => mapping(uint256 => mapping(uint256 => uint256[])))_tuple|) (F state_type) (G state_type) (H Int) (I tx_type) ) 
    (=>
      (and
        (summary_constructor_2_C_100_0 C H A B I F D G E)
        (and (= C 5)
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

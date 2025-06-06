(set-logic HORN)

(declare-datatypes ((|state_type| 0)) (((|state_type|  (|balances| (Array Int Int))))))
(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple|  (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))
(declare-datatypes ((|t_function_abiencodewithselector_pure(t_bytes4)returns(t_bytes_memory_ptr)_t_bytes4_t_uint256_t_uint256_t_uint256_t_uint256_t_bytes_memory_ptr_input| 0)) (((|t_function_abiencodewithselector_pure(t_bytes4)returns(t_bytes_memory_ptr)_t_bytes4_t_uint256_t_uint256_t_uint256_t_uint256_t_bytes_memory_ptr_input|  (|t_function_abiencodewithselector_pure(t_bytes4)returns(t_bytes_memory_ptr)_t_bytes4_t_uint256_t_uint256_t_uint256_t_uint256_t_bytes_memory_ptr_input_0| Int) (|t_function_abiencodewithselector_pure(t_bytes4)returns(t_bytes_memory_ptr)_t_bytes4_t_uint256_t_uint256_t_uint256_t_uint256_t_bytes_memory_ptr_input_1| Int) (|t_function_abiencodewithselector_pure(t_bytes4)returns(t_bytes_memory_ptr)_t_bytes4_t_uint256_t_uint256_t_uint256_t_uint256_t_bytes_memory_ptr_input_2| Int) (|t_function_abiencodewithselector_pure(t_bytes4)returns(t_bytes_memory_ptr)_t_bytes4_t_uint256_t_uint256_t_uint256_t_uint256_t_bytes_memory_ptr_input_3| Int) (|t_function_abiencodewithselector_pure(t_bytes4)returns(t_bytes_memory_ptr)_t_bytes4_t_uint256_t_uint256_t_uint256_t_uint256_t_bytes_memory_ptr_input_4| Int)))))
(declare-datatypes ((|t_function_abiencodewithsignature_pure(t_string_memory_ptr)returns(t_bytes_memory_ptr)_t_string_memory_ptr_t_uint256_t_uint256_t_uint256_t_uint256_t_bytes_memory_ptr_input| 0)) (((|t_function_abiencodewithsignature_pure(t_string_memory_ptr)returns(t_bytes_memory_ptr)_t_string_memory_ptr_t_uint256_t_uint256_t_uint256_t_uint256_t_bytes_memory_ptr_input|  (|t_function_abiencodewithsignature_pure(t_string_memory_ptr)returns(t_bytes_memory_ptr)_t_string_memory_ptr_t_uint256_t_uint256_t_uint256_t_uint256_t_bytes_memory_ptr_input_0| bytes_tuple) (|t_function_abiencodewithsignature_pure(t_string_memory_ptr)returns(t_bytes_memory_ptr)_t_string_memory_ptr_t_uint256_t_uint256_t_uint256_t_uint256_t_bytes_memory_ptr_input_1| Int) (|t_function_abiencodewithsignature_pure(t_string_memory_ptr)returns(t_bytes_memory_ptr)_t_string_memory_ptr_t_uint256_t_uint256_t_uint256_t_uint256_t_bytes_memory_ptr_input_2| Int) (|t_function_abiencodewithsignature_pure(t_string_memory_ptr)returns(t_bytes_memory_ptr)_t_string_memory_ptr_t_uint256_t_uint256_t_uint256_t_uint256_t_bytes_memory_ptr_input_3| Int) (|t_function_abiencodewithsignature_pure(t_string_memory_ptr)returns(t_bytes_memory_ptr)_t_string_memory_ptr_t_uint256_t_uint256_t_uint256_t_uint256_t_bytes_memory_ptr_input_4| Int)))))
(declare-datatypes ((|abi_type| 0)) (((|abi_type|  (|t_function_abiencodewithselector_pure(t_bytes4)returns(t_bytes_memory_ptr)_t_bytes4_t_uint256_t_uint256_t_uint256_t_uint256_t_bytes_memory_ptr| (Array |t_function_abiencodewithselector_pure(t_bytes4)returns(t_bytes_memory_ptr)_t_bytes4_t_uint256_t_uint256_t_uint256_t_uint256_t_bytes_memory_ptr_input|
       bytes_tuple)) (|t_function_abiencodewithsignature_pure(t_string_memory_ptr)returns(t_bytes_memory_ptr)_t_string_memory_ptr_t_uint256_t_uint256_t_uint256_t_uint256_t_bytes_memory_ptr| (Array |t_function_abiencodewithsignature_pure(t_string_memory_ptr)returns(t_bytes_memory_ptr)_t_string_memory_ptr_t_uint256_t_uint256_t_uint256_t_uint256_t_bytes_memory_ptr_input|
       bytes_tuple))))))
(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type|  (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))
(declare-datatypes ((|crypto_type| 0)) (((|crypto_type|  (|ecrecover| (Array ecrecover_input_type Int)) (|keccak256| (Array bytes_tuple Int)) (|ripemd160| (Array bytes_tuple Int)) (|sha256| (Array bytes_tuple Int))))))
(declare-datatypes ((|tx_type| 0)) (((|tx_type|  (|block.basefee| Int) (|block.chainid| Int) (|block.coinbase| Int) (|block.difficulty| Int) (|block.gaslimit| Int) (|block.number| Int) (|block.timestamp| Int) (|blockhash| (Array Int Int)) (|msg.data| bytes_tuple) (|msg.sender| Int) (|msg.sig| Int) (|msg.value| Int) (|tx.gasprice| Int) (|tx.origin| Int)))))

(declare-fun |contract_initializer_after_init_14_C_80_0| ( Int Int abi_type crypto_type tx_type state_type state_type ) Bool)
(declare-fun |block_7_return_function_abiEncodeHash__79_80_0| ( Int Int abi_type crypto_type tx_type state_type bytes_tuple Int Int state_type bytes_tuple Int Int bytes_tuple bytes_tuple bytes_tuple ) Bool)
(declare-fun |interface_0_C_80_0| ( Int abi_type crypto_type state_type ) Bool)
(declare-fun |block_6_abiEncodeHash_78_80_0| ( Int Int abi_type crypto_type tx_type state_type bytes_tuple Int Int state_type bytes_tuple Int Int bytes_tuple bytes_tuple bytes_tuple ) Bool)
(declare-fun |summary_constructor_2_C_80_0| ( Int Int abi_type crypto_type tx_type state_type state_type ) Bool)
(declare-fun |block_10_function_abiEncodeHash__79_80_0| ( Int Int abi_type crypto_type tx_type state_type bytes_tuple Int Int state_type bytes_tuple Int Int bytes_tuple bytes_tuple bytes_tuple ) Bool)
(declare-fun |block_8_function_abiEncodeHash__79_80_0| ( Int Int abi_type crypto_type tx_type state_type bytes_tuple Int Int state_type bytes_tuple Int Int bytes_tuple bytes_tuple bytes_tuple ) Bool)
(declare-fun |block_9_function_abiEncodeHash__79_80_0| ( Int Int abi_type crypto_type tx_type state_type bytes_tuple Int Int state_type bytes_tuple Int Int bytes_tuple bytes_tuple bytes_tuple ) Bool)
(declare-fun |contract_initializer_entry_13_C_80_0| ( Int Int abi_type crypto_type tx_type state_type state_type ) Bool)
(declare-fun |error_target_6_0| ( ) Bool)
(declare-fun |contract_initializer_12_C_80_0| ( Int Int abi_type crypto_type tx_type state_type state_type ) Bool)
(declare-fun |summary_3_function_abiEncodeHash__79_80_0| ( Int Int abi_type crypto_type tx_type state_type bytes_tuple Int Int state_type bytes_tuple Int Int ) Bool)
(declare-fun |implicit_constructor_entry_15_C_80_0| ( Int Int abi_type crypto_type tx_type state_type state_type ) Bool)
(declare-fun |summary_4_function_abiEncodeHash__79_80_0| ( Int Int abi_type crypto_type tx_type state_type bytes_tuple Int Int state_type bytes_tuple Int Int ) Bool)
(declare-fun |block_5_function_abiEncodeHash__79_80_0| ( Int Int abi_type crypto_type tx_type state_type bytes_tuple Int Int state_type bytes_tuple Int Int bytes_tuple bytes_tuple bytes_tuple ) Bool)
(declare-fun |block_11_function_abiEncodeHash__79_80_0| ( Int Int abi_type crypto_type tx_type state_type bytes_tuple Int Int state_type bytes_tuple Int Int bytes_tuple bytes_tuple bytes_tuple ) Bool)

(assert
  (forall ( (A Int) (B Int) (C abi_type) (D bytes_tuple) (E bytes_tuple) (F bytes_tuple) (G Int) (H Int) (I crypto_type) (J Int) (K bytes_tuple) (L bytes_tuple) (M state_type) (N state_type) (O Int) (P tx_type) ) 
    (=>
      (and
        true
      )
      (block_5_function_abiEncodeHash__79_80_0 J O C I P M K A G N L B H D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C abi_type) (D bytes_tuple) (E bytes_tuple) (F bytes_tuple) (G Int) (H Int) (I crypto_type) (J Int) (K bytes_tuple) (L bytes_tuple) (M state_type) (N state_type) (O Int) (P tx_type) ) 
    (=>
      (and
        (block_5_function_abiEncodeHash__79_80_0 J O C I P M K A G N L B H D E F)
        (and (= N M) (= J 0) (= H G) (= B A) (= L K))
      )
      (block_6_abiEncodeHash_78_80_0 J O C I P M K A G N L B H D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C abi_type) (D bytes_tuple) (E bytes_tuple) (F bytes_tuple) (G bytes_tuple) (H bytes_tuple) (I Int) (J Int) (K crypto_type) (L Int) (M Int) (N Int) (O Int) (P Bool) (Q bytes_tuple) (R Int) (S Int) (T Int) (U Int) (V bytes_tuple) (W bytes_tuple) (X Int) (Y Int) (Z Int) (A1 Int) (B1 bytes_tuple) (C1 bytes_tuple) (D1 Int) (E1 bytes_tuple) (F1 Int) (G1 Bool) (H1 bytes_tuple) (I1 bytes_tuple) (J1 state_type) (K1 state_type) (L1 Int) (M1 tx_type) ) 
    (=>
      (and
        (block_6_abiEncodeHash_78_80_0 L L1 C K M1 J1 H1 A I K1 I1 B J D F H)
        (and (= P (= N O))
     (= B1
        (select (|t_function_abiencodewithsignature_pure(t_string_memory_ptr)returns(t_bytes_memory_ptr)_t_string_memory_ptr_t_uint256_t_uint256_t_uint256_t_uint256_t_bytes_memory_ptr|
                  C)
                (|t_function_abiencodewithsignature_pure(t_string_memory_ptr)returns(t_bytes_memory_ptr)_t_string_memory_ptr_t_uint256_t_uint256_t_uint256_t_uint256_t_bytes_memory_ptr_input|
                  W
                  X
                  Y
                  Z
                  A1)))
     (= E V)
     (= E1 G)
     (= F (bytes_tuple ((as const (Array Int Int)) 0) 0))
     (= V
        (select (|t_function_abiencodewithsignature_pure(t_string_memory_ptr)returns(t_bytes_memory_ptr)_t_string_memory_ptr_t_uint256_t_uint256_t_uint256_t_uint256_t_bytes_memory_ptr|
                  C)
                (|t_function_abiencodewithsignature_pure(t_string_memory_ptr)returns(t_bytes_memory_ptr)_t_string_memory_ptr_t_uint256_t_uint256_t_uint256_t_uint256_t_bytes_memory_ptr_input|
                  Q
                  R
                  S
                  T
                  U)))
     (= Q I1)
     (= H (bytes_tuple ((as const (Array Int Int)) 0) 0))
     (= G B1)
     (= C1 E)
     (= D (bytes_tuple ((as const (Array Int Int)) 0) 0))
     (= W I1)
     (= A1 B)
     (= M 1)
     (= R B)
     (= D1 (select (keccak256 K) C1))
     (= X J)
     (= U B)
     (= O J)
     (= N B)
     (= T B)
     (= S B)
     (= F1 (select (keccak256 K) E1))
     (= Z J)
     (= Y B)
     (>= (bytes_tuple_accessor_length I1) 0)
     (>= A1 0)
     (>= R 0)
     (>= B 0)
     (>= D1 0)
     (>= X 0)
     (>= U 0)
     (>= O 0)
     (>= N 0)
     (>= J 0)
     (>= T 0)
     (>= S 0)
     (>= F1 0)
     (>= Z 0)
     (>= Y 0)
     (<= A1
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= R
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= B
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= D1
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= X
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= U
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= O
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= N
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= J
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= T
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= S
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= F1
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= Z
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= Y
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (not G1)
     (= P true)
     (= G1 (= D1 F1)))
      )
      (block_8_function_abiEncodeHash__79_80_0 M L1 C K M1 J1 H1 A I K1 I1 B J E G H)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C abi_type) (D bytes_tuple) (E bytes_tuple) (F bytes_tuple) (G Int) (H Int) (I crypto_type) (J Int) (K bytes_tuple) (L bytes_tuple) (M state_type) (N state_type) (O Int) (P tx_type) ) 
    (=>
      (and
        (block_8_function_abiEncodeHash__79_80_0 J O C I P M K A G N L B H D E F)
        true
      )
      (summary_3_function_abiEncodeHash__79_80_0 J O C I P M K A G N L B H)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C abi_type) (D bytes_tuple) (E bytes_tuple) (F bytes_tuple) (G Int) (H Int) (I crypto_type) (J Int) (K bytes_tuple) (L bytes_tuple) (M state_type) (N state_type) (O Int) (P tx_type) ) 
    (=>
      (and
        (block_9_function_abiEncodeHash__79_80_0 J O C I P M K A G N L B H D E F)
        true
      )
      (summary_3_function_abiEncodeHash__79_80_0 J O C I P M K A G N L B H)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C abi_type) (D bytes_tuple) (E bytes_tuple) (F bytes_tuple) (G Int) (H Int) (I crypto_type) (J Int) (K bytes_tuple) (L bytes_tuple) (M state_type) (N state_type) (O Int) (P tx_type) ) 
    (=>
      (and
        (block_10_function_abiEncodeHash__79_80_0 J O C I P M K A G N L B H D E F)
        true
      )
      (summary_3_function_abiEncodeHash__79_80_0 J O C I P M K A G N L B H)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C abi_type) (D bytes_tuple) (E bytes_tuple) (F bytes_tuple) (G Int) (H Int) (I crypto_type) (J Int) (K bytes_tuple) (L bytes_tuple) (M state_type) (N state_type) (O Int) (P tx_type) ) 
    (=>
      (and
        (block_7_return_function_abiEncodeHash__79_80_0 J O C I P M K A G N L B H D E F)
        true
      )
      (summary_3_function_abiEncodeHash__79_80_0 J O C I P M K A G N L B H)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C abi_type) (D bytes_tuple) (E bytes_tuple) (F bytes_tuple) (G bytes_tuple) (H bytes_tuple) (I bytes_tuple) (J Int) (K Int) (L crypto_type) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Bool) (S bytes_tuple) (T Int) (U Int) (V Int) (W Int) (X bytes_tuple) (Y bytes_tuple) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 bytes_tuple) (E1 bytes_tuple) (F1 Int) (G1 bytes_tuple) (H1 Int) (I1 Bool) (J1 bytes_tuple) (K1 Int) (L1 Int) (M1 Int) (N1 Int) (O1 bytes_tuple) (P1 bytes_tuple) (Q1 Int) (R1 bytes_tuple) (S1 Int) (T1 Bool) (U1 bytes_tuple) (V1 bytes_tuple) (W1 state_type) (X1 state_type) (Y1 Int) (Z1 tx_type) ) 
    (=>
      (and
        (block_6_abiEncodeHash_78_80_0 M Y1 C L Z1 W1 U1 A J X1 V1 B K D F H)
        (and (= I1 (= F1 H1))
     (= R (= P Q))
     (= E1 E)
     (= X
        (select (|t_function_abiencodewithsignature_pure(t_string_memory_ptr)returns(t_bytes_memory_ptr)_t_string_memory_ptr_t_uint256_t_uint256_t_uint256_t_uint256_t_bytes_memory_ptr|
                  C)
                (|t_function_abiencodewithsignature_pure(t_string_memory_ptr)returns(t_bytes_memory_ptr)_t_string_memory_ptr_t_uint256_t_uint256_t_uint256_t_uint256_t_bytes_memory_ptr_input|
                  S
                  T
                  U
                  V
                  W)))
     (= O1
        (select (|t_function_abiencodewithselector_pure(t_bytes4)returns(t_bytes_memory_ptr)_t_bytes4_t_uint256_t_uint256_t_uint256_t_uint256_t_bytes_memory_ptr|
                  C)
                (|t_function_abiencodewithselector_pure(t_bytes4)returns(t_bytes_memory_ptr)_t_bytes4_t_uint256_t_uint256_t_uint256_t_uint256_t_bytes_memory_ptr_input|
                  1713907968
                  K1
                  L1
                  M1
                  N1)))
     (= E X)
     (= F (bytes_tuple ((as const (Array Int Int)) 0) 0))
     (= G D1)
     (= H (bytes_tuple ((as const (Array Int Int)) 0) 0))
     (= R1 I)
     (= S V1)
     (= Y V1)
     (= I O1)
     (= D1
        (select (|t_function_abiencodewithsignature_pure(t_string_memory_ptr)returns(t_bytes_memory_ptr)_t_string_memory_ptr_t_uint256_t_uint256_t_uint256_t_uint256_t_bytes_memory_ptr|
                  C)
                (|t_function_abiencodewithsignature_pure(t_string_memory_ptr)returns(t_bytes_memory_ptr)_t_string_memory_ptr_t_uint256_t_uint256_t_uint256_t_uint256_t_bytes_memory_ptr_input|
                  Y
                  Z
                  A1
                  B1
                  C1)))
     (= D (bytes_tuple ((as const (Array Int Int)) 0) 0))
     (= P1 E)
     (= G1 G)
     (= (select (bytes_tuple_accessor_array J1) 2) 41)
     (= (select (bytes_tuple_accessor_array J1) 1) 40)
     (= (select (bytes_tuple_accessor_array J1) 0) 102)
     (= (bytes_tuple_accessor_length J1) 3)
     (= N M)
     (= N1 B)
     (= Z K)
     (= T B)
     (= Q K)
     (= P B)
     (= O 2)
     (= Q1 (select (keccak256 L) P1))
     (= K1 B)
     (= H1 (select (keccak256 L) G1))
     (= C1 B)
     (= B1 K)
     (= A1 B)
     (= W B)
     (= V B)
     (= U B)
     (= F1 (select (keccak256 L) E1))
     (= S1 (select (keccak256 L) R1))
     (= M1 B)
     (= L1 B)
     (>= (bytes_tuple_accessor_length V1) 0)
     (>= N1 0)
     (>= Z 0)
     (>= T 0)
     (>= B 0)
     (>= Q 0)
     (>= P 0)
     (>= K 0)
     (>= Q1 0)
     (>= K1 0)
     (>= H1 0)
     (>= C1 0)
     (>= B1 0)
     (>= A1 0)
     (>= W 0)
     (>= V 0)
     (>= U 0)
     (>= F1 0)
     (>= S1 0)
     (>= M1 0)
     (>= L1 0)
     (<= N1
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= Z
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= T
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= B
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= Q
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= P
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= K
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= Q1
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= K1
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= H1
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= C1
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= B1
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= A1
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= W
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= V
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= U
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= F1
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= S1
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= M1
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= L1
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (not T1)
     (= R true)
     (= T1 (= Q1 S1)))
      )
      (block_9_function_abiEncodeHash__79_80_0 O Y1 C L Z1 W1 U1 A J X1 V1 B K E G I)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C abi_type) (D bytes_tuple) (E bytes_tuple) (F bytes_tuple) (G bytes_tuple) (H bytes_tuple) (I bytes_tuple) (J Int) (K Int) (L crypto_type) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Bool) (T bytes_tuple) (U Int) (V Int) (W Int) (X Int) (Y bytes_tuple) (Z bytes_tuple) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 bytes_tuple) (F1 bytes_tuple) (G1 Int) (H1 bytes_tuple) (I1 Int) (J1 Bool) (K1 bytes_tuple) (L1 Int) (M1 Int) (N1 Int) (O1 Int) (P1 bytes_tuple) (Q1 bytes_tuple) (R1 Int) (S1 bytes_tuple) (T1 Int) (U1 Bool) (V1 bytes_tuple) (W1 Int) (X1 bytes_tuple) (Y1 Int) (Z1 Bool) (A2 bytes_tuple) (B2 bytes_tuple) (C2 state_type) (D2 state_type) (E2 Int) (F2 tx_type) ) 
    (=>
      (and
        (block_6_abiEncodeHash_78_80_0 M E2 C L F2 C2 A2 A J D2 B2 B K D F H)
        (and (= J1 (= G1 I1))
     (= U1 (= R1 T1))
     (= S (= Q R))
     (= E Y)
     (= H (bytes_tuple ((as const (Array Int Int)) 0) 0))
     (= X1 I)
     (= Y
        (select (|t_function_abiencodewithsignature_pure(t_string_memory_ptr)returns(t_bytes_memory_ptr)_t_string_memory_ptr_t_uint256_t_uint256_t_uint256_t_uint256_t_bytes_memory_ptr|
                  C)
                (|t_function_abiencodewithsignature_pure(t_string_memory_ptr)returns(t_bytes_memory_ptr)_t_string_memory_ptr_t_uint256_t_uint256_t_uint256_t_uint256_t_bytes_memory_ptr_input|
                  T
                  U
                  V
                  W
                  X)))
     (= Q1 E)
     (= E1
        (select (|t_function_abiencodewithsignature_pure(t_string_memory_ptr)returns(t_bytes_memory_ptr)_t_string_memory_ptr_t_uint256_t_uint256_t_uint256_t_uint256_t_bytes_memory_ptr|
                  C)
                (|t_function_abiencodewithsignature_pure(t_string_memory_ptr)returns(t_bytes_memory_ptr)_t_string_memory_ptr_t_uint256_t_uint256_t_uint256_t_uint256_t_bytes_memory_ptr_input|
                  Z
                  A1
                  B1
                  C1
                  D1)))
     (= H1 G)
     (= Z B2)
     (= I P1)
     (= G E1)
     (= F (bytes_tuple ((as const (Array Int Int)) 0) 0))
     (= D (bytes_tuple ((as const (Array Int Int)) 0) 0))
     (= V1 E)
     (= S1 I)
     (= F1 E)
     (= T B2)
     (= P1
        (select (|t_function_abiencodewithselector_pure(t_bytes4)returns(t_bytes_memory_ptr)_t_bytes4_t_uint256_t_uint256_t_uint256_t_uint256_t_bytes_memory_ptr|
                  C)
                (|t_function_abiencodewithselector_pure(t_bytes4)returns(t_bytes_memory_ptr)_t_bytes4_t_uint256_t_uint256_t_uint256_t_uint256_t_bytes_memory_ptr_input|
                  1713907968
                  L1
                  M1
                  N1
                  O1)))
     (= (select (bytes_tuple_accessor_array K1) 2) 41)
     (= (select (bytes_tuple_accessor_array K1) 1) 40)
     (= (select (bytes_tuple_accessor_array K1) 0) 102)
     (= (bytes_tuple_accessor_length K1) 3)
     (= T1 (select (keccak256 L) S1))
     (= W B)
     (= V B)
     (= U B)
     (= R K)
     (= Q B)
     (= P 3)
     (= O N)
     (= W1 (select (keccak256 L) V1))
     (= O1 B)
     (= N1 B)
     (= I1 (select (keccak256 L) H1))
     (= G1 (select (keccak256 L) F1))
     (= D1 B)
     (= C1 K)
     (= B1 B)
     (= A1 K)
     (= X B)
     (= N M)
     (= M1 B)
     (= L1 B)
     (= Y1 (select (keccak256 L) X1))
     (= R1 (select (keccak256 L) Q1))
     (>= (bytes_tuple_accessor_length B2) 0)
     (>= T1 0)
     (>= B 0)
     (>= W 0)
     (>= V 0)
     (>= U 0)
     (>= R 0)
     (>= Q 0)
     (>= K 0)
     (>= W1 0)
     (>= O1 0)
     (>= N1 0)
     (>= I1 0)
     (>= G1 0)
     (>= D1 0)
     (>= C1 0)
     (>= B1 0)
     (>= A1 0)
     (>= X 0)
     (>= M1 0)
     (>= L1 0)
     (>= Y1 0)
     (>= R1 0)
     (<= T1
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= B
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= W
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= V
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= U
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= R
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= Q
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= K
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= W1
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= O1
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= N1
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= I1
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= G1
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= D1
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= C1
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= B1
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= A1
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= X
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= M1
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= L1
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= Y1
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= R1
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (not Z1)
     (= S true)
     (not (= (= W1 Y1) Z1)))
      )
      (block_10_function_abiEncodeHash__79_80_0 P E2 C L F2 C2 A2 A J D2 B2 B K E G I)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C abi_type) (D bytes_tuple) (E bytes_tuple) (F bytes_tuple) (G bytes_tuple) (H bytes_tuple) (I bytes_tuple) (J Int) (K Int) (L crypto_type) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Bool) (T bytes_tuple) (U Int) (V Int) (W Int) (X Int) (Y bytes_tuple) (Z bytes_tuple) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 bytes_tuple) (F1 bytes_tuple) (G1 Int) (H1 bytes_tuple) (I1 Int) (J1 Bool) (K1 bytes_tuple) (L1 Int) (M1 Int) (N1 Int) (O1 Int) (P1 bytes_tuple) (Q1 bytes_tuple) (R1 Int) (S1 bytes_tuple) (T1 Int) (U1 Bool) (V1 bytes_tuple) (W1 Int) (X1 bytes_tuple) (Y1 Int) (Z1 Bool) (A2 bytes_tuple) (B2 bytes_tuple) (C2 state_type) (D2 state_type) (E2 Int) (F2 tx_type) ) 
    (=>
      (and
        (block_6_abiEncodeHash_78_80_0 M E2 C L F2 C2 A2 A J D2 B2 B K D F H)
        (and (= J1 (= G1 I1))
     (= U1 (= R1 T1))
     (= S (= Q R))
     (= E Y)
     (= H (bytes_tuple ((as const (Array Int Int)) 0) 0))
     (= X1 I)
     (= Y
        (select (|t_function_abiencodewithsignature_pure(t_string_memory_ptr)returns(t_bytes_memory_ptr)_t_string_memory_ptr_t_uint256_t_uint256_t_uint256_t_uint256_t_bytes_memory_ptr|
                  C)
                (|t_function_abiencodewithsignature_pure(t_string_memory_ptr)returns(t_bytes_memory_ptr)_t_string_memory_ptr_t_uint256_t_uint256_t_uint256_t_uint256_t_bytes_memory_ptr_input|
                  T
                  U
                  V
                  W
                  X)))
     (= Q1 E)
     (= E1
        (select (|t_function_abiencodewithsignature_pure(t_string_memory_ptr)returns(t_bytes_memory_ptr)_t_string_memory_ptr_t_uint256_t_uint256_t_uint256_t_uint256_t_bytes_memory_ptr|
                  C)
                (|t_function_abiencodewithsignature_pure(t_string_memory_ptr)returns(t_bytes_memory_ptr)_t_string_memory_ptr_t_uint256_t_uint256_t_uint256_t_uint256_t_bytes_memory_ptr_input|
                  Z
                  A1
                  B1
                  C1
                  D1)))
     (= H1 G)
     (= Z B2)
     (= I P1)
     (= G E1)
     (= F (bytes_tuple ((as const (Array Int Int)) 0) 0))
     (= D (bytes_tuple ((as const (Array Int Int)) 0) 0))
     (= V1 E)
     (= S1 I)
     (= F1 E)
     (= T B2)
     (= P1
        (select (|t_function_abiencodewithselector_pure(t_bytes4)returns(t_bytes_memory_ptr)_t_bytes4_t_uint256_t_uint256_t_uint256_t_uint256_t_bytes_memory_ptr|
                  C)
                (|t_function_abiencodewithselector_pure(t_bytes4)returns(t_bytes_memory_ptr)_t_bytes4_t_uint256_t_uint256_t_uint256_t_uint256_t_bytes_memory_ptr_input|
                  1713907968
                  L1
                  M1
                  N1
                  O1)))
     (= (select (bytes_tuple_accessor_array K1) 2) 41)
     (= (select (bytes_tuple_accessor_array K1) 1) 40)
     (= (select (bytes_tuple_accessor_array K1) 0) 102)
     (= (bytes_tuple_accessor_length K1) 3)
     (= T1 (select (keccak256 L) S1))
     (= W B)
     (= V B)
     (= U B)
     (= R K)
     (= Q B)
     (= P O)
     (= O N)
     (= W1 (select (keccak256 L) V1))
     (= O1 B)
     (= N1 B)
     (= I1 (select (keccak256 L) H1))
     (= G1 (select (keccak256 L) F1))
     (= D1 B)
     (= C1 K)
     (= B1 B)
     (= A1 K)
     (= X B)
     (= N M)
     (= M1 B)
     (= L1 B)
     (= Y1 (select (keccak256 L) X1))
     (= R1 (select (keccak256 L) Q1))
     (>= (bytes_tuple_accessor_length B2) 0)
     (>= T1 0)
     (>= B 0)
     (>= W 0)
     (>= V 0)
     (>= U 0)
     (>= R 0)
     (>= Q 0)
     (>= K 0)
     (>= W1 0)
     (>= O1 0)
     (>= N1 0)
     (>= I1 0)
     (>= G1 0)
     (>= D1 0)
     (>= C1 0)
     (>= B1 0)
     (>= A1 0)
     (>= X 0)
     (>= M1 0)
     (>= L1 0)
     (>= Y1 0)
     (>= R1 0)
     (<= T1
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= B
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= W
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= V
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= U
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= R
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= Q
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= K
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= W1
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= O1
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= N1
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= I1
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= G1
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= D1
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= C1
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= B1
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= A1
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= X
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= M1
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= L1
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= Y1
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (<= R1
         115792089237316195423570985008687907853269984665640564039457584007913129639935)
     (= S true)
     (not (= (= W1 Y1) Z1)))
      )
      (block_7_return_function_abiEncodeHash__79_80_0
  P
  E2
  C
  L
  F2
  C2
  A2
  A
  J
  D2
  B2
  B
  K
  E
  G
  I)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C abi_type) (D bytes_tuple) (E bytes_tuple) (F bytes_tuple) (G Int) (H Int) (I crypto_type) (J Int) (K bytes_tuple) (L bytes_tuple) (M state_type) (N state_type) (O Int) (P tx_type) ) 
    (=>
      (and
        true
      )
      (block_11_function_abiEncodeHash__79_80_0 J O C I P M K A G N L B H D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D abi_type) (E bytes_tuple) (F bytes_tuple) (G bytes_tuple) (H Int) (I Int) (J Int) (K crypto_type) (L Int) (M Int) (N Int) (O bytes_tuple) (P bytes_tuple) (Q bytes_tuple) (R state_type) (S state_type) (T state_type) (U state_type) (V Int) (W tx_type) ) 
    (=>
      (and
        (block_11_function_abiEncodeHash__79_80_0 L V D K W R O A H S P B I E F G)
        (summary_3_function_abiEncodeHash__79_80_0 M V D K W T P B I U Q C J)
        (let ((a!1 (store (balances S) V (+ (select (balances S) V) N)))
      (a!2 (= (select (bytes_tuple_accessor_array (msg.data W)) 3) 95))
      (a!3 (= (select (bytes_tuple_accessor_array (msg.data W)) 2) 51))
      (a!4 (= (select (bytes_tuple_accessor_array (msg.data W)) 1) 31))
      (a!5 (= (select (bytes_tuple_accessor_array (msg.data W)) 0) 222))
      (a!6 (>= (+ (select (balances S) V) N) 0))
      (a!7 (<= (+ (select (balances S) V) N)
               115792089237316195423570985008687907853269984665640564039457584007913129639935)))
  (and (= T (state_type a!1))
       (= S R)
       a!2
       a!3
       a!4
       a!5
       (= (msg.value W) 0)
       (= (msg.sig W) 3726586719)
       (= B A)
       (= L 0)
       (= I H)
       (>= (tx.origin W) 0)
       (>= (tx.gasprice W) 0)
       (>= (msg.value W) 0)
       (>= (msg.sender W) 0)
       (>= (block.timestamp W) 0)
       (>= (block.number W) 0)
       (>= (block.gaslimit W) 0)
       (>= (block.difficulty W) 0)
       (>= (block.coinbase W) 0)
       (>= (block.chainid W) 0)
       (>= (block.basefee W) 0)
       (>= (bytes_tuple_accessor_length (msg.data W)) 4)
       a!6
       (>= N (msg.value W))
       (<= (tx.origin W) 1461501637330902918203684832716283019655932542975)
       (<= (tx.gasprice W)
           115792089237316195423570985008687907853269984665640564039457584007913129639935)
       (<= (msg.value W)
           115792089237316195423570985008687907853269984665640564039457584007913129639935)
       (<= (msg.sender W) 1461501637330902918203684832716283019655932542975)
       (<= (block.timestamp W)
           115792089237316195423570985008687907853269984665640564039457584007913129639935)
       (<= (block.number W)
           115792089237316195423570985008687907853269984665640564039457584007913129639935)
       (<= (block.gaslimit W)
           115792089237316195423570985008687907853269984665640564039457584007913129639935)
       (<= (block.difficulty W)
           115792089237316195423570985008687907853269984665640564039457584007913129639935)
       (<= (block.coinbase W) 1461501637330902918203684832716283019655932542975)
       (<= (block.chainid W)
           115792089237316195423570985008687907853269984665640564039457584007913129639935)
       (<= (block.basefee W)
           115792089237316195423570985008687907853269984665640564039457584007913129639935)
       a!7
       (= P O)))
      )
      (summary_4_function_abiEncodeHash__79_80_0 M V D K W R O A H U Q C J)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C abi_type) (D Int) (E Int) (F crypto_type) (G Int) (H bytes_tuple) (I bytes_tuple) (J state_type) (K state_type) (L Int) (M tx_type) ) 
    (=>
      (and
        (summary_4_function_abiEncodeHash__79_80_0 G L C F M J H A D K I B E)
        (interface_0_C_80_0 L C F J)
        (= G 0)
      )
      (interface_0_C_80_0 L C F K)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D state_type) (E state_type) (F Int) (G tx_type) ) 
    (=>
      (and
        (summary_constructor_2_C_80_0 C F A B G D E)
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
      (interface_0_C_80_0 F A B E)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D state_type) (E state_type) (F Int) (G tx_type) ) 
    (=>
      (and
        (and (= C 0) (= E D))
      )
      (contract_initializer_entry_13_C_80_0 C F A B G D E)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D state_type) (E state_type) (F Int) (G tx_type) ) 
    (=>
      (and
        (contract_initializer_entry_13_C_80_0 C F A B G D E)
        true
      )
      (contract_initializer_after_init_14_C_80_0 C F A B G D E)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D state_type) (E state_type) (F Int) (G tx_type) ) 
    (=>
      (and
        (contract_initializer_after_init_14_C_80_0 C F A B G D E)
        true
      )
      (contract_initializer_12_C_80_0 C F A B G D E)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D state_type) (E state_type) (F Int) (G tx_type) ) 
    (=>
      (and
        (and (= C 0) (>= (select (balances E) F) (msg.value G)) (= E D))
      )
      (implicit_constructor_entry_15_C_80_0 C F A B G D E)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D Int) (E state_type) (F state_type) (G state_type) (H Int) (I tx_type) ) 
    (=>
      (and
        (implicit_constructor_entry_15_C_80_0 C H A B I E F)
        (contract_initializer_12_C_80_0 D H A B I F G)
        (not (<= D 0))
      )
      (summary_constructor_2_C_80_0 D H A B I E G)
    )
  )
)
(assert
  (forall ( (A abi_type) (B crypto_type) (C Int) (D Int) (E state_type) (F state_type) (G state_type) (H Int) (I tx_type) ) 
    (=>
      (and
        (contract_initializer_12_C_80_0 D H A B I F G)
        (implicit_constructor_entry_15_C_80_0 C H A B I E F)
        (= D 0)
      )
      (summary_constructor_2_C_80_0 D H A B I E G)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C abi_type) (D Int) (E Int) (F crypto_type) (G Int) (H bytes_tuple) (I bytes_tuple) (J state_type) (K state_type) (L Int) (M tx_type) ) 
    (=>
      (and
        (summary_4_function_abiEncodeHash__79_80_0 G L C F M J H A D K I B E)
        (interface_0_C_80_0 L C F J)
        (= G 2)
      )
      error_target_6_0
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        error_target_6_0
        true
      )
      false
    )
  )
)

(check-sat)
(exit)

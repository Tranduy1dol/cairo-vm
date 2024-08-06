use std::collections::HashMap;
use std::ops::Deref;

use crate::hint_processor::builtin_hint_processor::hint_utils::{
    get_constant_from_var_name, get_integer_from_var_name, get_ptr_from_var_name,
    insert_value_from_var_name, insert_value_into_ap,
};
use crate::hint_processor::builtin_hint_processor::uint256_utils::Uint256;
use crate::hint_processor::hint_processor_definition::HintReference;
use crate::math_utils::signed_felt;
use crate::serde::deserialize_program::ApTracking;
use crate::types::errors::math_errors::MathError;
use crate::types::exec_scope::ExecutionScopes;
use crate::vm::errors::hint_errors::HintError;
use crate::vm::vm_core::VirtualMachine;
use crate::Felt252;
use num_bigint::{BigInt, BigUint};
use num_integer::Integer;
use num_traits::Zero;
use num_traits::{FromPrimitive, One};

use super::bigint_utils::BigInt3;
use super::ec_utils::EcPoint;
use super::secp_utils::{SECP256R1_ALPHA, SECP256R1_B, SECP256R1_P};

pub const MAYBE_WRITE_ADDRESS_TO_AP: &str = r#"memory[ap] = to_felt_or_relocatable(ids.response.ec_point.address_ if ids.not_on_curve == 0 else segments.add())"#;
pub fn maybe_write_address_to_ap(
    vm: &mut VirtualMachine,
    _exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    _ap_tracking: &ApTracking,
    _constants: &HashMap<String, Felt252>,
) -> Result<(), HintError> {
    let not_on_curve = get_integer_from_var_name("not_on_curve", vm, ids_data, _ap_tracking)?;
    if not_on_curve == Felt252::ZERO {
        let response = get_ptr_from_var_name("response", vm, ids_data, _ap_tracking)?;
        let offset = 1; // SecpNewResponse::ec_point_offset()
        let ec_point = vm.get_relocatable((response + offset)?)?; //TODO: Use actual struct offset
        insert_value_into_ap(vm, ec_point)?;
    } else {
        let segment = vm.add_memory_segment();
        insert_value_into_ap(vm, segment)?;
    }
    Ok(())
}

pub const PACK_X_PRIME: &str = r#"from starkware.cairo.common.cairo_secp.secp256r1_utils import SECP256R1_P
from starkware.cairo.common.cairo_secp.secp_utils import pack
value = pack(ids.x, PRIME) % SECP256R1_P"#;
pub fn pack_x_prime(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
    _constants: &HashMap<String, Felt252>,
) -> Result<(), HintError> {
    let x = BigInt3::from_var_name("x", vm, ids_data, ap_tracking)?.pack86();
    exec_scopes.insert_value("value", x.mod_floor(&SECP256R1_P));
    Ok(())
}

pub const COMPUTE_Q_MOD_PRIME: &str = r#"from starkware.cairo.common.cairo_secp.secp256r1_utils import SECP256R1_P
from starkware.cairo.common.cairo_secp.secp_utils import pack

q, r = divmod(pack(ids.val, PRIME), SECP256R1_P)
assert r == 0, f"verify_zero: Invalid input {ids.val.d0, ids.val.d1, ids.val.d2}."
ids.q = q % PRIME"#;
pub fn compute_q_mod_prime(
    vm: &mut VirtualMachine,
    _exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
    _constants: &HashMap<String, Felt252>,
) -> Result<(), HintError> {
    let val = BigInt3::from_var_name("val", vm, ids_data, ap_tracking)?.pack86();
    let (q, r) = val.div_rem(&SECP256R1_P);
    if !r.is_zero() {
        return Err(HintError::SecpVerifyZero(Box::new(val)));
    }
    insert_value_from_var_name("q", Felt252::from(&q), vm, ids_data, ap_tracking)?;
    Ok(())
}

pub const COMPUTE_IDS_HIGH_LOW: &str = r#"from starkware.cairo.common.math_utils import as_int

# Correctness check.
value = as_int(ids.value, PRIME) % PRIME
assert value < ids.UPPER_BOUND, f'{value} is outside of the range [0, 2**165).'

# Calculation for the assertion.
ids.high, ids.low = divmod(ids.value, ids.SHIFT)"#;
pub fn compute_ids_high_low(
    vm: &mut VirtualMachine,
    _exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
    constants: &HashMap<String, Felt252>,
) -> Result<(), HintError> {
    const UPPER_BOUND: &str = "starkware.cairo.common.math.assert_250_bit.UPPER_BOUND";
    const SHIFT: &str = "starkware.cairo.common.math.assert_250_bit.SHIFT";
    //Declare constant values
    let upper_bound = constants
        .get(UPPER_BOUND)
        .map_or_else(|| get_constant_from_var_name("UPPER_BOUND", constants), Ok)?;
    let shift = constants
        .get(SHIFT)
        .map_or_else(|| get_constant_from_var_name("SHIFT", constants), Ok)?;
    let value = Felt252::from(&signed_felt(get_integer_from_var_name(
        "value",
        vm,
        ids_data,
        ap_tracking,
    )?));
    if &value > upper_bound {
        return Err(HintError::ValueOutside250BitRange(Box::new(value)));
    }

    let (high, low) = value.div_rem(&shift.try_into().map_err(|_| MathError::DividedByZero)?);
    insert_value_from_var_name("high", high, vm, ids_data, ap_tracking)?;
    insert_value_from_var_name("low", low, vm, ids_data, ap_tracking)?;
    Ok(())
}

pub const CALCULATE_VALUE: &str = r#"from starkware.cairo.common.cairo_secp.secp_utils import SECP256R1, pack
from starkware.python.math_utils import y_squared_from_x

y_square_int = y_squared_from_x(
    x=pack(ids.x, SECP256R1.prime),
    alpha=SECP256R1.alpha,
    beta=SECP256R1.beta,
    field_prime=SECP256R1.prime,
)

# Note that (y_square_int ** ((SECP256R1.prime + 1) / 4)) ** 2 =
#   = y_square_int ** ((SECP256R1.prime + 1) / 2) =
#   = y_square_int ** ((SECP256R1.prime - 1) / 2 + 1) =
#   = y_square_int * y_square_int ** ((SECP256R1.prime - 1) / 2) = y_square_int * {+/-}1.
y = pow(y_square_int, (SECP256R1.prime + 1) // 4, SECP256R1.prime)

# We need to decide whether to take y or prime - y.
if ids.v % 2 == y % 2:
    value = y
else:
    value = (-y) % SECP256R1.prime"#;

pub fn calculate_value(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
    _constants: &HashMap<String, Felt252>,
) -> Result<(), HintError> {
    // def y_squared_from_x(x: int, alpha: int, beta: int, field_prime: int) -> int:
    // """
    // Computes y^2 using the curve equation:
    // y^2 = x^3 + alpha * x + beta (mod field_prime)
    // """
    // return (pow(x, 3, field_prime) + alpha * x + beta) % field_prime
    fn y_squared_from_x(x: &BigInt, alpha: &BigInt, beta: &BigInt, field_prime: &BigInt) -> BigInt {
        use std::ops::{Add, Mul, Rem};
        // Compute x^3 (mod field_prime)
        let x_cubed = x.modpow(&BigInt::from(3), &field_prime);

        // Compute alpha * x
        let alpha_x = alpha.mul(x);

        // Compute y^2 = (x^3 + alpha * x + beta) % field_prime
        let y_squared = x_cubed.add(&alpha_x).add(beta).rem(field_prime);

        y_squared
    }

    // prime = curve.prime
    //     y_squared = y_squared_from_x(
    //         x=x,
    //         alpha=curve.alpha,
    //         beta=curve.beta,
    //         field_prime=prime,
    //     )

    //     y = pow(y_squared, (prime + 1) // 4, prime)
    //     if (y & 1) != request.y_parity:
    //         y = (-y) % prime

    let x = BigInt3::from_var_name("x", vm, ids_data, ap_tracking)?
        .pack86()
        .mod_floor(&SECP256R1_P);

    let y_square_int = y_squared_from_x(&x, &SECP256R1_ALPHA, &SECP256R1_B, &SECP256R1_P);
    exec_scopes.insert_value::<BigInt>("y_square_int", y_square_int.clone());

    // Calculate (prime + 1) // 4
    let exp = (SECP256R1_P.to_owned() + BigInt::one()).div_floor(&BigInt::from(4));
    // Calculate pow(y_square_int, exp, prime)
    let y = y_square_int.modpow(&exp, &SECP256R1_P);
    exec_scopes.insert_value::<BigInt>("y", y.clone());

    let v = get_integer_from_var_name("v", vm, ids_data, ap_tracking)?;
    let v = BigInt::from(v.to_biguint());
    if v % 2 == y.clone() % 2 {
        exec_scopes.insert_value("value", y);
    } else {
        let value = (-y).mod_floor(&SECP256R1_P);
        exec_scopes.insert_value("value", value);
    }
    Ok(())
}

pub const IS_ON_CURVE_2: &str = r#"ids.is_on_curve = (y * y) % SECP256R1.prime == y_square_int"#;

pub fn is_on_curve_2(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
    _constants: &HashMap<String, Felt252>,
) -> Result<(), HintError> {
    let y: BigInt = exec_scopes.get("y")?;
    let y_square_int: BigInt = exec_scopes.get("y_square_int")?;

    let is_on_curve = ((y.pow(2)) % SECP256R1_P.to_owned()) == y_square_int;
    insert_value_from_var_name(
        "is_on_curve",
        Felt252::from(is_on_curve),
        vm,
        ids_data,
        ap_tracking,
    )?;

    Ok(())
}

pub const CALCULATE_VALUE_2: &str = r#"from starkware.cairo.common.cairo_secp.secp256r1_utils import SECP256R1_P
from starkware.cairo.common.cairo_secp.secp_utils import pack

slope = pack(ids.slope, SECP256R1_P)
x = pack(ids.point.x, SECP256R1_P)
y = pack(ids.point.y, SECP256R1_P)

value = new_x = (pow(slope, 2, SECP256R1_P) - 2 * x) % SECP256R1_P"#;

pub fn calculate_value_2(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
    _constants: &HashMap<String, Felt252>,
) -> Result<(), HintError> {
    exec_scopes.insert_value::<BigInt>("SECP256R1_P", SECP256R1_P.clone());
    //ids.slope
    let slope = BigInt3::from_var_name("slope", vm, ids_data, ap_tracking)?;
    //ids.point
    let point = EcPoint::from_var_name("point", vm, ids_data, ap_tracking)?;

    let slope = slope.pack86().mod_floor(&SECP256R1_P);
    let x = point.x.pack86().mod_floor(&SECP256R1_P);
    let y = point.y.pack86().mod_floor(&SECP256R1_P);

    let value = (slope.pow(2) - (&x << 1u32)).mod_floor(&SECP256R1_P);

    //Assign variables to vm scope
    exec_scopes.insert_value("slope", slope);
    exec_scopes.insert_value("x", x);
    exec_scopes.insert_value("y", y);
    exec_scopes.insert_value("value", value.clone());
    exec_scopes.insert_value("new_x", value);
    Ok(())
}

#[allow(unused)]
pub const GENERATE_NIBBLES: &str = r#"num = (ids.scalar.high << 128) + ids.scalar.low
nibbles = [(num >> i) & 0xf for i in range(0, 256, 4)]
ids.first_nibble = nibbles.pop()
ids.last_nibble = nibbles[0]"#;
pub fn generate_nibbles(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    ids_data: &HashMap<String, HintReference>,
    ap_tracking: &ApTracking,
    _constants: &HashMap<String, Felt252>,
) -> Result<(), HintError> {
    let num = Uint256::from_var_name("scalar", vm, ids_data, ap_tracking)?.pack();

    // Generate nibbles
    let mut nibbles: Vec<Felt252> = (0..256)
        .step_by(4)
        .map(|i| ((&num >> i) & BigUint::from_u8(0xf).unwrap()))
        .map(|s: BigUint| s.into())
        .collect();

    // ids.first_nibble = nibbles.pop()
    let first_nibble = nibbles.pop().unwrap();

    insert_value_from_var_name(
        "first_nibble",
        Felt252::from(first_nibble),
        vm,
        ids_data,
        ap_tracking,
    )?;

    // ids.last_nibble = nibbles[0]
    let last_nibble = *nibbles.get(0).unwrap();
    insert_value_from_var_name(
        "last_nibble",
        Felt252::from(last_nibble),
        vm,
        ids_data,
        ap_tracking,
    )?;
    exec_scopes.insert_value("nibbles", nibbles);
    Ok(())
}

pub const FAST_SECP_ADD_ASSIGN_NEW_Y: &str =
    r#"value = new_y = (slope * (x - new_x) - y) % SECP256R1_P"#;
pub fn fast_secp_add_assign_new_y(
    _vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    _ids_data: &HashMap<String, HintReference>,
    _ap_tracking: &ApTracking,
    _constants: &HashMap<String, Felt252>,
) -> Result<(), HintError> {
    //Get variables from vm scope
    let (slope, x, new_x, y, secp_p) = (
        exec_scopes.get::<BigInt>("slope")?,
        exec_scopes.get::<BigInt>("x")?,
        exec_scopes.get::<BigInt>("new_x")?,
        exec_scopes.get::<BigInt>("y")?,
        SECP256R1_P.deref(),
    );
    let value = (slope * (x - new_x) - y).mod_floor(secp_p);
    exec_scopes.insert_value("value", value.clone());
    exec_scopes.insert_value("new_y", value);

    Ok(())
}

pub const WRITE_NIBBLES_TO_MEM: &str = r#"memory[fp + 0] = to_felt_or_relocatable(nibbles.pop())"#;

pub fn write_nibbles_to_mem(
    vm: &mut VirtualMachine,
    exec_scopes: &mut ExecutionScopes,
    _ids_data: &HashMap<String, HintReference>,
    _ap_tracking: &ApTracking,
    _constants: &HashMap<String, Felt252>,
) -> Result<(), HintError> {
    let nibbles: &mut Vec<Felt252> = exec_scopes.get_mut_list_ref("nibbles")?;
    let nibble = nibbles.pop().unwrap();
    vm.insert_value((vm.get_fp() + 0)?, nibble)?;

    Ok(())
}

#[cfg(test)]
mod tests {

    use std::ops::Deref;

    use assert_matches::assert_matches;
    use rstest::rstest;

    use crate::utils::test_utils::*;

    use super::*;

    #[rstest]
    fn test_set_ap_to_ec_point_address() {
        let mut vm = VirtualMachine::new(false);

        let ap_tracking = ApTracking::default();

        let mut exec_scopes = ExecutionScopes::new();

        vm.run_context.fp = 4;
        vm.set_ap(4);
        // Create hint_data
        let ids_data = non_continuous_ids_data![("not_on_curve", -2), ("response", -1)];
        vm.segments = segments![((1, 0), 0), ((1, 1), (2, 0)), ((1, 2), 0), ((1, 3), (1, 0))];
        maybe_write_address_to_ap(
            &mut vm,
            &mut exec_scopes,
            &ids_data,
            &ap_tracking,
            &Default::default(),
        )
        .expect("maybe_write_address_to_ap() failed");

        let ap = vm.get_ap();

        let ec_point = vm.get_relocatable(ap).unwrap();
        assert_eq!(ec_point, (2, 0).into());
    }
    #[test]
    fn test_is_on_curve_2() {
        let mut vm = VirtualMachine::new(false);
        vm.set_fp(1);
        let ids_data = ids_data!["is_on_curve"];
        let ap_tracking = ApTracking::default();

        let mut exec_scopes = ExecutionScopes::new();

        let y = BigInt::from(1234);
        let y_square_int = y.clone() * y.clone();

        exec_scopes.insert_value("y", y);
        exec_scopes.insert_value("y_square_int", y_square_int);

        is_on_curve_2(
            &mut vm,
            &mut exec_scopes,
            &ids_data,
            &ap_tracking,
            &Default::default(),
        )
        .expect("is_on_curve2() failed");

        let is_on_curve: Felt252 =
            get_integer_from_var_name("is_on_curve", &vm, &ids_data, &ap_tracking)
                .expect("is_on_curve2 should be put in ids_data");
        assert_eq!(is_on_curve, 1.into());
    }
    #[test]
    fn test_compute_q_mod_prime() {
        let mut vm = VirtualMachine::new(false);

        let ap_tracking = ApTracking::default();

        let mut exec_scopes = ExecutionScopes::new();

        vm.run_context.fp = 9;
        //Create hint data
        let ids_data = non_continuous_ids_data![("val", -5), ("q", 0)];
        vm.segments = segments![((1, 4), 0), ((1, 5), 0), ((1, 6), 0)];
        compute_q_mod_prime(
            &mut vm,
            &mut exec_scopes,
            &ids_data,
            &ap_tracking,
            &Default::default(),
        )
        .expect("compute_q_mod_prime() failed");

        let q: Felt252 = get_integer_from_var_name("q", &vm, &ids_data, &ap_tracking)
            .expect("compute_q_mod_prime should have put 'q' in ids_data");
        assert_eq!(q, Felt252::from(0));
    }

    #[test]
    fn test_compute_ids_high_low() {
        let mut vm = VirtualMachine::new(false);

        let value = BigInt::from(25);
        let shift = BigInt::from(12);

        vm.set_fp(14);
        let ids_data = non_continuous_ids_data![
            ("UPPER_BOUND", -14),
            ("value", -11),
            ("high", -8),
            ("low", -5),
            ("SHIFT", -2)
        ];

        vm.segments = segments!(
            //UPPER_BOUND
            ((1, 0), 18446744069414584321),
            ((1, 1), 0),
            ((1, 2), 0),
            //value
            ((1, 3), 25),
            ((1, 4), 0),
            ((1, 5), 0),
            //high
            ((1, 6), 2),
            ((1, 7), 0),
            ((1, 8), 0),
            //low
            ((1, 9), 1),
            ((1, 10), 0),
            ((1, 11), 0),
            //SHIFT
            ((1, 12), 12),
            ((1, 13), 0),
            ((1, 14), 0)
        );

        let ap_tracking = ApTracking::default();

        let mut exec_scopes = ExecutionScopes::new();

        let constants = HashMap::new();
        compute_ids_high_low(
            &mut vm,
            &mut exec_scopes,
            &ids_data,
            &ap_tracking,
            &constants,
        )
        .expect("compute_ids_high_low() failed");

        let high: Felt252 = get_integer_from_var_name("high", &vm, &ids_data, &ap_tracking)
            .expect("compute_ids_high_low should have put 'high' in ids_data");
        let low: Felt252 = get_integer_from_var_name("low", &vm, &ids_data, &ap_tracking)
            .expect("compute_ids_high_low should have put 'low' in ids_data");

        let (expected_high, expected_low) = value.div_rem(&shift);
        assert_eq!(high, Felt252::from(expected_high));
        assert_eq!(low, Felt252::from(expected_low));
    }
    #[test]
    fn test_calculate_value() {
        let mut vm = VirtualMachine::new(false);
        vm.set_fp(10);

        let ids_data = non_continuous_ids_data![("x", -10), ("v", -7)];
        vm.segments = segments!(
            // X
            ((1, 0), 18446744069414584321),
            ((1, 1), 0),
            ((1, 2), 0),
            // v
            ((1, 3), 1),
            ((1, 4), 0),
            ((1, 5), 0),
        );
        let ap_tracking = ApTracking::default();

        let mut exec_scopes = ExecutionScopes::new();

        let x = BigInt::from(18446744069414584321u128); // Example x value
        let v = BigInt::from(1); // Example v value (must be 0 or 1 for even/odd check)

        let constants = HashMap::new();

        calculate_value(
            &mut vm,
            &mut exec_scopes,
            &ids_data,
            &ap_tracking,
            &constants,
        )
        .expect("calculate_value() failed");

        let value: BigInt = exec_scopes
            .get("value")
            .expect("value should be calculated and stored in exec_scopes");

        // Compute y_squared_from_x(x)
        let y_square_int = (x.modpow(&BigInt::from(3), &SECP256R1_P)
            + SECP256R1_ALPHA.deref() * &x
            + SECP256R1_B.deref())
        .mod_floor(&SECP256R1_P);

        // Calculate y = pow(y_square_int, (SECP256R1_P + 1) // 4, SECP256R1_P)
        let exp = (SECP256R1_P.deref() + BigInt::one()).div_floor(&BigInt::from(4));
        let y = y_square_int.modpow(&exp, &SECP256R1_P);

        // Determine the expected value based on the parity of v and y
        let expected_value = if v % 2 == y.clone() % 2 {
            y
        } else {
            (-y).mod_floor(&SECP256R1_P)
        };

        assert_eq!(value, expected_value);
    }

    #[test]
    fn test_pack_x_prime() {
        let mut vm = VirtualMachine::new(false);

        //Initialize fp
        vm.run_context.fp = 10;

        //Create hint data
        let ids_data = non_continuous_ids_data![("x", -5)];

        vm.segments = segments![
            ((1, 5), ("132181232131231239112312312313213083892150", 10)),
            ((1, 6), 10),
            ((1, 7), 10)
        ];

        let ap_tracking = ApTracking::default();

        let mut exec_scopes = ExecutionScopes::new();

        pack_x_prime(
            &mut vm,
            &mut exec_scopes,
            &ids_data,
            &ap_tracking,
            &Default::default(),
        )
        .expect("pack_x_prime() failed");

        assert_matches!(
            exec_scopes.get::<BigInt>("value"),
            Ok(x) if x == bigint_str!(
                "59863107065205964761754162760883789350782881856141750"
            )
        );
    }
}

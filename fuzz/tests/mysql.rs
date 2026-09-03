use diesel::mysql::MysqlType;
use diesel::mysql::data_types::{MysqlTime, MysqlTimestampType};
use diesel_fuzz::mysql::{
    CASES, TYPES, carries_date_fields, decode_case, differential, known_validation_split,
};

const MYSQL_TIME_SIZE: usize = std::mem::size_of::<MysqlTime>();

/// Zero-filled, which also satisfies the `neg` byte check in `time_value`.
fn zero_buf(len: usize) -> Vec<u8> {
    vec![0u8; len]
}

fn valid_datetime_buf() -> Vec<u8> {
    MysqlTime::new(
        2024,
        6,
        15,
        12,
        30,
        45,
        500_000,
        false,
        MysqlTimestampType::MYSQL_TIMESTAMP_DATETIME,
        0,
    )
    .serialize()
    .to_vec()
}

fn valid_date_buf() -> Vec<u8> {
    MysqlTime::new(
        2024,
        6,
        15,
        0,
        0,
        0,
        0,
        false,
        MysqlTimestampType::MYSQL_TIMESTAMP_DATE,
        0,
    )
    .serialize()
    .to_vec()
}

fn valid_time_buf() -> Vec<u8> {
    MysqlTime::new(
        0,
        0,
        0,
        10,
        30,
        45,
        500_000,
        false,
        MysqlTimestampType::MYSQL_TIMESTAMP_TIME,
        0,
    )
    .serialize()
    .to_vec()
}

fn type_idx(tpe: MysqlType) -> u8 {
    let pos = TYPES.iter().position(|t| *t == tpe).expect("type in TYPES");
    u8::try_from(pos).expect("TYPES.len() < 256")
}

/// Every case and wire type, at the five boundary lengths.
#[test]
fn decode_case_never_panics() {
    let short = zero_buf(MYSQL_TIME_SIZE.saturating_sub(1));
    let exact = valid_datetime_buf();
    let mut over = valid_datetime_buf(); // fresh call; no clone
    over.push(0x00);
    let buffers: &[&[u8]] = &[
        &[],     // 0 bytes
        &[0x00], // 1 byte
        &short,  // size_of::<MysqlTime>() - 1
        &exact,  // exact size_of::<MysqlTime>()
        &over,   // size_of::<MysqlTime>() + 1
    ];

    for (c_idx, _case) in CASES.iter().enumerate() {
        let sel = u8::try_from(c_idx).expect("CASES.len() < 256");
        for (t_idx, _tpe) in TYPES.iter().enumerate() {
            let tsel = u8::try_from(t_idx).expect("TYPES.len() < 256");
            for buf in buffers {
                decode_case(sel, tsel, buf);
            }
        }
    }
}

#[test]
fn differential_agrees_on_datetime() {
    let buf = valid_datetime_buf();
    let dt_tsel = type_idx(MysqlType::DateTime);
    // selector 2 → diff_datetime
    assert!(
        differential(2, dt_tsel, &buf).is_none(),
        "chrono and time disagree on a valid Datetime buffer"
    );
}

#[test]
fn differential_agrees_on_timestamp() {
    let buf = valid_datetime_buf();
    let ts_tsel = type_idx(MysqlType::Timestamp);
    // selector 3 → diff_timestamp
    assert!(
        differential(3, ts_tsel, &buf).is_none(),
        "chrono and time disagree on a valid Timestamp buffer"
    );
}

#[test]
fn differential_agrees_on_date() {
    let buf = valid_date_buf();
    let d_tsel = type_idx(MysqlType::Date);
    // selector 0 → diff_date
    assert!(
        differential(0, d_tsel, &buf).is_none(),
        "chrono and time disagree on a valid Date buffer"
    );
}

#[test]
fn differential_agrees_on_time() {
    let buf = valid_time_buf();
    let t_tsel = type_idx(MysqlType::Time);
    // selector 1 → diff_time
    assert!(
        differential(1, t_tsel, &buf).is_none(),
        "chrono and time disagree on a valid Time buffer"
    );
}

/// Witness; delete with the fix.
#[test]
fn datetime_tz_displacement_differs_between_chrono_and_time() {
    let bytes: &[u8] = &[
        0x26, 0x00, 0x00, 0x00, 0x04, 0x00, 0x00, 0x00, 0x04, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x71, 0x71, 0x00, 0x00, 0x00, 0x00,
        0x00, 0xFF, 0xFF, 0xFF, 0x94, 0x71,
    ];
    let tpe = TYPES[113 % TYPES.len()];
    assert!(
        known_validation_split(bytes, tpe),
        "the field is what differs"
    );
    // skipped by that field, so every other disagreement stays a finding
    assert!(differential(10, 113, bytes).is_none());
}

/// Witness; delete with the fix.
#[test]
fn time_of_day_with_a_displacement_is_refused_only_by_time() {
    let buf = MysqlTime::new(
        0,
        0,
        0,
        10,
        30,
        45,
        0,
        false,
        MysqlTimestampType::MYSQL_TIMESTAMP_TIME,
        48_384,
    )
    .serialize()
    .to_vec();
    let tpe = MysqlType::Time;
    assert!(known_validation_split(&buf, tpe));
    assert!(differential(1, type_idx(tpe), &buf).is_none());
}

/// Witness; delete with the fix.
#[test]
fn a_time_of_day_carrying_a_date_is_refused_only_by_time() {
    let buf = MysqlTime::new(
        2024,
        6,
        15,
        10,
        30,
        45,
        0,
        false,
        MysqlTimestampType::MYSQL_TIMESTAMP_TIME,
        0,
    )
    .serialize()
    .to_vec();
    let tpe = MysqlType::Time;
    assert!(carries_date_fields(&buf, tpe));
    assert!(!known_validation_split(&buf, tpe));
    assert!(differential(1, type_idx(tpe), &buf).is_none());
}

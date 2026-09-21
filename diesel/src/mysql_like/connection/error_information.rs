#![allow(unsafe_code)] // module uses ffi
use core::ffi::{CStr, c_char};

use crate::result::DatabaseErrorInformation;

/// The error information Diesel keeps for a MySQL or MariaDB error.
#[derive(Debug)]
pub(crate) struct MysqlLikeErrorInformation {
    pub(crate) message: String,
    pub(crate) sqlstate: Option<String>,
}

/// Copies the SQLSTATE that the client library reported for a failed handle.
pub(crate) fn sqlstate_from_ptr(sqlstate: *const c_char) -> Option<String> {
    if sqlstate.is_null() {
        return None;
    }
    // SAFETY: the caller passes the result of `mysql_sqlstate` or
    // `mysql_stmt_sqlstate`, which is either null or a NUL terminated buffer
    // owned by the connection or statement handle that the caller still borrows.
    let sqlstate = unsafe { CStr::from_ptr(sqlstate) };
    sqlstate.to_str().ok().map(str::to_owned)
}

impl DatabaseErrorInformation for MysqlLikeErrorInformation {
    fn message(&self) -> &str {
        &self.message
    }

    fn details(&self) -> Option<&str> {
        None
    }

    fn hint(&self) -> Option<&str> {
        None
    }

    fn table_name(&self) -> Option<&str> {
        None
    }

    fn column_name(&self) -> Option<&str> {
        None
    }

    fn constraint_name(&self) -> Option<&str> {
        None
    }

    fn statement_position(&self) -> Option<i32> {
        None
    }

    fn sqlstate(&self) -> Option<&str> {
        self.sqlstate.as_deref()
    }
}

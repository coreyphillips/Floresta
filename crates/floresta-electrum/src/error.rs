// SPDX-License-Identifier: MIT OR Apache-2.0

use thiserror::Error;
use tokio::sync::oneshot;

#[derive(Error, Debug)]
pub enum Error {
    #[error("Transaction history unavailable in local watch index")]
    HistoryUnavailable,

    #[error("Invalid params passed in")]
    InvalidParams,

    #[error("Invalid json string {0}")]
    Parsing(#[from] serde_json::Error),

    #[error("Blockchain error")]
    Blockchain(Box<dyn core::error::Error + Send + 'static>),

    #[error("IO error")]
    Io(#[from] std::io::Error),

    #[error("Mempool accept error")]
    Mempool(Box<dyn core::error::Error + Send + 'static>),

    #[error("Node isn't working")]
    NodeInterface(#[from] oneshot::error::RecvError),
}

impl Error {
    pub(super) fn rpc_reply(&self, id: serde_json::Value) -> serde_json::Value {
        // A selective cache miss cannot establish that a transaction never existed.
        let (code, message) = match self {
            Self::HistoryUnavailable => (-32004, self.to_string()),
            _ => (-32000, String::from("Internal JSON-RPC error.")),
        };
        serde_json::json!({ "jsonrpc": "2.0", "error": { "code": code, "message": message, "data": null }, "id": id })
    }
}

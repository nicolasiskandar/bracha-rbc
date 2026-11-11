use crate::message::InstanceId;

#[derive(thiserror::Error, Debug)]
pub enum ProtocolError {
    #[error("wrong instance: expected {expected:?}, got {got:?}")]
    WrongInstance {
        expected: InstanceId,
        got: InstanceId,
    },

    #[error("INIT from non-broadcaster: sender={sender}, broadcaster={broadcaster}")]
    InitFromNonBroadcaster { sender: u32, broadcaster: u32 },

    #[error("malformed or empty message")]
    Malformed,
}

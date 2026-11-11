use serde::{Deserialize, Serialize};

pub type ProcessId = u32;

pub type Value = Vec<u8>;

#[derive(Clone, Debug, Hash, Eq, PartialEq, Serialize, Deserialize)]
pub struct InstanceId(pub u64);

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Message {
    Init { instance: InstanceId, value: Value },

    Echo { instance: InstanceId, value: Value },

    Ready { instance: InstanceId, value: Value },
}

impl Message {
    pub fn instance(&self) -> &InstanceId {
        match self {
            Message::Init { instance, .. }
            | Message::Echo { instance, .. }
            | Message::Ready { instance, .. } => instance,
        }
    }

    pub fn value(&self) -> &Value {
        match self {
            Message::Init { value, .. }
            | Message::Echo { value, .. }
            | Message::Ready { value, .. } => value,
        }
    }

    pub fn kind(&self) -> MessageKind {
        match self {
            Message::Init { .. } => MessageKind::Init,
            Message::Echo { .. } => MessageKind::Echo,
            Message::Ready { .. } => MessageKind::Ready,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MessageKind {
    Init,
    Echo,
    Ready,
}

impl std::fmt::Display for MessageKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MessageKind::Init => write!(f, "INIT"),
            MessageKind::Echo => write!(f, "ECHO"),
            MessageKind::Ready => write!(f, "READY"),
        }
    }
}

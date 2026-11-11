use crate::{
    errors::ProtocolError,
    message::{InstanceId, Message, ProcessId, Value},
    state::ProcessState,
    thresholds::Config,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Action {
    Broadcast(Message),

    Deliver { instance: InstanceId, value: Value },
}

pub struct BroadcastInstance {
    pub id: InstanceId,

    pub process_id: ProcessId,

    pub broadcaster: ProcessId,

    pub config: Config,

    pub state: ProcessState,
}

impl BroadcastInstance {
    pub fn new(
        id: InstanceId,
        process_id: ProcessId,
        broadcaster: ProcessId,
        config: Config,
    ) -> Self {
        BroadcastInstance {
            id,
            process_id,
            broadcaster,
            config,
            state: ProcessState::new(),
        }
    }

    pub fn handle_message(
        &mut self,
        authenticated_sender: ProcessId,
        message: &Message,
    ) -> Result<Vec<Action>, ProtocolError> {
        if message.instance() != &self.id {
            return Err(ProtocolError::WrongInstance {
                expected: self.id.clone(),
                got: message.instance().clone(),
            });
        }

        if message.value().is_empty() {
            return Err(ProtocolError::Malformed);
        }

        let actions = match message {
            Message::Init { value, .. } => {
                if authenticated_sender != self.broadcaster {
                    return Err(ProtocolError::InitFromNonBroadcaster {
                        sender: authenticated_sender,
                        broadcaster: self.broadcaster,
                    });
                }
                self.on_init(value)
            }
            Message::Echo { value, .. } => self.on_echo(authenticated_sender, value),
            Message::Ready { value, .. } => self.on_ready(authenticated_sender, value),
        };

        Ok(actions)
    }

    pub fn initiate(&mut self, value: Value) -> Vec<Action> {
        let mut actions = vec![Action::Broadcast(Message::Init {
            instance: self.id.clone(),
            value: value.clone(),
        })];

        actions.extend(self.on_init(&value));
        actions
    }

    fn on_init(&mut self, value: &Value) -> Vec<Action> {
        if self.state.echo_sent.is_some() {
            return vec![];
        }

        self.state.echo_sent = Some(value.clone());

        let mut actions = vec![Action::Broadcast(Message::Echo {
            instance: self.id.clone(),
            value: value.clone(),
        })];

        self.state.record_echo(self.process_id, value.clone());
        actions.extend(self.check_rules(value));
        actions
    }

    fn on_echo(&mut self, sender: ProcessId, value: &Value) -> Vec<Action> {
        self.state.record_echo(sender, value.clone());
        self.check_rules(value)
    }

    fn on_ready(&mut self, sender: ProcessId, value: &Value) -> Vec<Action> {
        self.state.record_ready(sender, value.clone());
        self.check_rules(value)
    }

    fn check_rules(&mut self, value: &Value) -> Vec<Action> {
        let mut actions = Vec::new();

        if self.state.ready_sent.is_none() {
            let echo_met = self.state.echo_count(value) >= self.config.echo_threshold();
            let ready_amplify_met =
                self.state.ready_count(value) >= self.config.ready_amplify_threshold();

            if echo_met || ready_amplify_met {
                self.state.ready_sent = Some(value.clone());
                self.state.record_ready(self.process_id, value.clone());
                actions.push(Action::Broadcast(Message::Ready {
                    instance: self.id.clone(),
                    value: value.clone(),
                }));
            }
        }

        if self.state.delivered.is_none()
            && self.state.ready_count(value) >= self.config.deliver_threshold()
        {
            self.state.delivered = Some(value.clone());
            actions.push(Action::Deliver {
                instance: self.id.clone(),
                value: value.clone(),
            });
        }

        actions
    }
}

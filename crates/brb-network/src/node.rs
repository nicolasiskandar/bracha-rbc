use crate::transport;
use brb_core::{Action, BroadcastInstance, Config, InstanceId, ProcessId, Value};
use std::collections::HashMap;
use std::net::SocketAddr;
use std::sync::Arc;
use tokio::net::TcpStream;
use tokio::sync::Mutex;

pub struct Node {
    pub id: ProcessId,
    pub listen_addr: SocketAddr,
    instance: Arc<Mutex<BroadcastInstance>>,
    peers: Arc<Mutex<HashMap<ProcessId, TcpStream>>>,
}

impl Node {
    pub fn new(
        id: ProcessId,
        listen_addr: SocketAddr,
        broadcaster: ProcessId,
        config: Config,
        instance_id: InstanceId,
    ) -> Self {
        Node {
            id,
            listen_addr,
            instance: Arc::new(Mutex::new(BroadcastInstance::new(
                instance_id,
                id,
                broadcaster,
                config,
            ))),
            peers: Arc::new(Mutex::new(HashMap::new())),
        }
    }

    pub async fn connect_to_peer(
        &self,
        peer_id: ProcessId,
        addr: SocketAddr,
    ) -> std::io::Result<()> {
        let stream = TcpStream::connect(addr).await?;
        self.peers.lock().await.insert(peer_id, stream);
        Ok(())
    }

    pub async fn initiate(&self, value: Value) {
        let actions = self.instance.lock().await.initiate(value);
        self.execute_actions(actions).await;
    }

    async fn execute_actions(&self, actions: Vec<Action>) {
        let mut peers = self.peers.lock().await;
        for action in actions {
            if let Action::Broadcast(ref message) = action {
                for (_, stream) in peers.iter_mut() {
                    let _ = transport::send_message(stream, message).await;
                }
            }
        }
    }
}

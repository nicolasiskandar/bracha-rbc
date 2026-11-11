use crate::transport;
use brb_core::Message;
use brb_core::{Action, BroadcastInstance, ProcessId};
use std::sync::Arc;
use tokio::net::TcpStream;
use tokio::sync::Mutex;

pub async fn handle_peer(
    peer_id: ProcessId,
    mut stream: TcpStream,
    instance: Arc<Mutex<BroadcastInstance>>,
    tx: tokio::sync::mpsc::Sender<(ProcessId, Vec<Action>)>,
) {
    loop {
        match transport::recv_message::<Message>(&mut stream).await {
            Ok(message) => {
                let mut inst = instance.lock().await;
                match inst.handle_message(peer_id, &message) {
                    Ok(actions) => {
                        let _ = tx.send((peer_id, actions)).await;
                    }
                    Err(e) => {
                        tracing::warn!("rejected message from {peer_id}: {e}");
                    }
                }
            }
            Err(e) => {
                tracing::info!("peer {peer_id} disconnected: {e}");
                break;
            }
        }
    }
}

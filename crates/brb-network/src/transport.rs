use serde::{de::DeserializeOwned, Serialize};
use std::io;
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::TcpStream;

pub async fn send_message<T: Serialize>(stream: &mut TcpStream, msg: &T) -> io::Result<()> {
    let encoded =
        serde_json::to_vec(msg).map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;
    let len = encoded.len() as u32;
    stream.write_all(&len.to_be_bytes()).await?;
    stream.write_all(&encoded).await?;
    Ok(())
}

pub async fn recv_message<T: DeserializeOwned>(stream: &mut TcpStream) -> io::Result<T> {
    let mut len_buf = [0u8; 4];
    stream.read_exact(&mut len_buf).await?;
    let len = u32::from_be_bytes(len_buf) as usize;
    if len > 16 * 1024 * 1024 {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "message too large",
        ));
    }
    let mut buf = vec![0u8; len];
    stream.read_exact(&mut buf).await?;
    serde_json::from_slice(&buf).map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))
}

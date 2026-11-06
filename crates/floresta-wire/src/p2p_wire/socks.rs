// SPDX-License-Identifier: MIT OR Apache-2.0

//! A wrapper around a TCP stream that handles the SOCKS5 handshake. This module only
//! drives the handshake and returns the stream back to the caller. It does not
//! perform any I/O on the stream after the handshake is complete. The caller is
//! responsible for performing I/O on the stream.
//! This module is built on top of the `futures` crate instead of an specific
//! async runtime. This allows the caller to use this module with any async runtime
//! they want.

use core::error;
use core::fmt;
use core::fmt::Display;
use core::fmt::Formatter;
use core::net::Ipv4Addr;
use core::net::Ipv6Addr;
use core::net::SocketAddr;

use bitcoin::p2p::address::AddrV2;
use tokio::io::AsyncRead;
use tokio::io::AsyncReadExt;
use tokio::io::AsyncWrite;
use tokio::io::AsyncWriteExt;

#[derive(Clone, Debug)]
pub struct Socks5StreamBuilder {
    pub address: SocketAddr,
}
/// The version of the SOCKS protocol we support, only SOCKS5 is supported.
const SOCKS_VERSION: u8 = 5;
/// The SOCKS authentication method we support, only no authentication is supported.
const SOCKS_AUTH_METHOD_NONE: u8 = 0;
/// The cmd value for a SOCKS5 connect request.
const SOCKS_CMD_CONNECT: u8 = 1;
/// Magic value to indicate an IPv4 address.
const SOCKS_ADDR_TYPE_IPV4: u8 = 1;
/// Magic value to indicate a domain address.
const SOCKS_ADDR_TYPE_DOMAIN: u8 = 3;
/// Magic value to indicate an IPv6 address.
const SOCKS_ADDR_TYPE_IPV6: u8 = 4;

#[derive(Clone, Debug)]
#[allow(dead_code)]
pub enum Socks5Addr {
    Ipv4(Ipv4Addr),
    Ipv6(Ipv6Addr),
    Domain(Box<[u8]>),
}
impl Socks5Addr {
    fn address_type(&self) -> u8 {
        match self {
            Socks5Addr::Ipv4(_) => SOCKS_ADDR_TYPE_IPV4,
            Socks5Addr::Ipv6(_) => SOCKS_ADDR_TYPE_IPV6,
            Socks5Addr::Domain(_) => SOCKS_ADDR_TYPE_DOMAIN,
        }
    }
}
impl From<Socks5Addr> for u8 {
    fn from(address: Socks5Addr) -> Self {
        address.address_type()
    }
}

impl TryFrom<AddrV2> for Socks5Addr {
    type Error = Socks5Error;

    fn try_from(address: AddrV2) -> Result<Self, Self::Error> {
        let domain = match address {
            AddrV2::Ipv4(ip) => return Ok(Self::Ipv4(ip)),
            AddrV2::Ipv6(ip) | AddrV2::Cjdns(ip) => return Ok(Self::Ipv6(ip)),
            AddrV2::TorV3(key) => {
                // BIP 155 carries only the public key. Restore the onion
                // checksum and version before asking the proxy for the name.
                let version = [3];
                let preimage = [b".onion checksum".as_slice(), &key, &version].concat();
                let checksum = bitcoin_hashes::Sha3_256::hash(&preimage);
                let address = [&key[..], &checksum.as_byte_array()[..2], &version].concat();
                data_encoding::BASE32_NOPAD
                    .encode(&address)
                    .to_ascii_lowercase()
                    + ".onion"
            }
            AddrV2::I2p(hash) => {
                data_encoding::BASE32_NOPAD
                    .encode(&hash)
                    .to_ascii_lowercase()
                    + ".b32.i2p"
            }
            AddrV2::TorV2(_) | AddrV2::Unknown(_, _) => return Err(Socks5Error::InvalidAddress),
        };
        Ok(Self::Domain(domain.into_bytes().into_boxed_slice()))
    }
}

impl Socks5StreamBuilder {
    pub fn new(address: SocketAddr) -> Self {
        Self { address }
    }
    pub async fn connect<Stream: AsyncRead + AsyncWrite + Unpin>(
        mut socket: Stream,
        address: &Socks5Addr,
        port: u16,
    ) -> Result<Stream, Socks5Error> {
        let address_type = address.address_type();
        let address = match address {
            Socks5Addr::Ipv4(addr) => addr.octets().to_vec(),
            Socks5Addr::Ipv6(addr) => addr.octets().to_vec(),
            Socks5Addr::Domain(domain) => {
                let length = u8::try_from(domain.len()).map_err(|_| Socks5Error::InvalidAddress)?;
                if length == 0 {
                    return Err(Socks5Error::InvalidAddress);
                }
                let mut buf = vec![length];
                buf.extend_from_slice(domain);
                buf
            }
        };
        socket
            .write_all(&[SOCKS_VERSION, 1, SOCKS_AUTH_METHOD_NONE])
            .await?;
        let mut buf = [0_u8; 2];
        socket.read_exact(&mut buf).await?;

        if buf[0] != SOCKS_VERSION {
            return Err(Socks5Error::InvalidVersion);
        }

        if buf[1] != SOCKS_AUTH_METHOD_NONE {
            return Err(Socks5Error::InvalidAuthMethod);
        }

        socket
            .write_all(&[SOCKS_VERSION, SOCKS_CMD_CONNECT, 0, address_type])
            .await?;
        socket.write_all(&address).await?;
        socket.write_all(&port.to_be_bytes()).await?;

        let mut buf = [0_u8; 4];
        socket.read_exact(&mut buf).await?;

        if buf[0] != SOCKS_VERSION {
            return Err(Socks5Error::InvalidVersion);
        }
        if buf[1] != 0 {
            return Err(Socks5Error::ConnectionFailed);
        }

        match buf[3] {
            SOCKS_ADDR_TYPE_IPV4 => {
                let mut buf = [0_u8; 6];
                socket.read_exact(&mut buf).await?;
            }
            SOCKS_ADDR_TYPE_IPV6 => {
                let mut buf = [0_u8; 18];
                socket.read_exact(&mut buf).await?;
            }
            SOCKS_ADDR_TYPE_DOMAIN => {
                let mut buf = [0_u8; 1];
                socket.read_exact(&mut buf).await?;
                let mut buf = vec![0_u8; buf[0] as usize + 2];
                socket.read_exact(&mut buf).await?;
            }
            _ => return Err(Socks5Error::ConnectionFailed),
        }
        Ok(socket)
    }
}
#[derive(Debug)]
pub enum Socks5Error {
    InvalidVersion,
    InvalidAuthMethod,
    ConnectionFailed,
    InvalidAddress,
    ReadError,
}

impl From<tokio::io::Error> for Socks5Error {
    fn from(_error: tokio::io::Error) -> Self {
        Socks5Error::ReadError
    }
}

impl Display for Socks5Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Socks5Error::InvalidVersion => write!(f, "Invalid SOCKS version"),
            Socks5Error::InvalidAuthMethod => write!(f, "Invalid authentication method"),
            Socks5Error::ConnectionFailed => write!(f, "Connection failed"),
            Socks5Error::InvalidAddress => write!(f, "Invalid address"),
            Socks5Error::ReadError => write!(f, "Error reading from socket"),
        }
    }
}

impl error::Error for Socks5Error {}

#[cfg(test)]
mod tests {
    use super::*;

    async fn request(address: Socks5Addr, expected: &[u8]) {
        let (client, mut proxy) = tokio::io::duplex(1024);
        let capture = async {
            let mut hello = [0; 3];
            proxy.read_exact(&mut hello).await.unwrap();
            assert_eq!(hello, [5, 1, 0]);
            proxy.write_all(&[5, 0]).await.unwrap();
            let mut bytes = vec![0; expected.len()];
            proxy.read_exact(&mut bytes).await.unwrap();
            proxy
                .write_all(&[5, 0, 0, 1, 127, 0, 0, 1, 0, 0])
                .await
                .unwrap();
            bytes
        };
        let (result, bytes) = tokio::join!(
            Socks5StreamBuilder::connect(client, &address, 8333),
            capture
        );
        result.unwrap();
        assert_eq!(bytes, expected);
    }

    #[tokio::test]
    async fn ipv4_connect_bytes() {
        request(
            Socks5Addr::Ipv4("192.0.2.1".parse().unwrap()),
            &[5, 1, 0, 1, 192, 0, 2, 1, 0x20, 0x8d],
        )
        .await;
    }

    #[tokio::test]
    async fn ipv6_connect_bytes() {
        request(
            Socks5Addr::Ipv6("2001:db8::1".parse().unwrap()),
            &[
                5, 1, 0, 4, 0x20, 1, 0x0d, 0xb8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0x20, 0x8d,
            ],
        )
        .await;
    }

    #[tokio::test]
    async fn domain_connect_bytes() {
        request(
            Socks5Addr::Domain(b"peer.invalid".as_slice().into()),
            b"\x05\x01\x00\x03\x0cpeer.invalid\x20\x8d",
        )
        .await;
    }

    #[tokio::test]
    async fn closed_proxy_returns_error() {
        let (client, peer) = tokio::io::duplex(32);
        drop(peer);
        let addr = Socks5Addr::Ipv4(Ipv4Addr::LOCALHOST);
        assert!(matches!(
            Socks5StreamBuilder::connect(client, &addr, 8333).await,
            Err(Socks5Error::ReadError)
        ));
    }
    #[tokio::test]
    async fn proxy_refusal_returns_an_error() {
        let (client, mut proxy) = tokio::io::duplex(64);
        proxy.write_all(&[5, 0, 5, 5, 0, 1]).await.unwrap();
        let addr = Socks5Addr::Ipv4(Ipv4Addr::LOCALHOST);
        assert!(matches!(
            Socks5StreamBuilder::connect(client, &addr, 8333).await,
            Err(Socks5Error::ConnectionFailed)
        ));
    }

    #[tokio::test]
    async fn domain_length_is_bounded() {
        let max = vec![b'a'; 255];
        let mut expected = vec![5, 1, 0, 3, 255];
        expected.extend_from_slice(&max);
        expected.extend_from_slice(&8333_u16.to_be_bytes());
        request(Socks5Addr::Domain(max.into()), &expected).await;

        for len in [0, 256] {
            let (client, mut proxy) = tokio::io::duplex(32);
            let addr = Socks5Addr::Domain(vec![b'a'; len].into());
            assert!(matches!(
                Socks5StreamBuilder::connect(client, &addr, 8333).await,
                Err(Socks5Error::InvalidAddress)
            ));
            assert_eq!(proxy.read(&mut [0]).await.unwrap(), 0);
        }
    }

    #[tokio::test]
    async fn bip155_names_are_sent_as_text() {
        let bytes = core::array::from_fn(|index| index as u8);
        for (address, name) in [
            (
                AddrV2::TorV3(bytes),
                "aaaqeayeaudaocajbifqydiob4ibceqtcqkrmfyydenbwha5dyp3kead.onion",
            ),
            (
                AddrV2::I2p(bytes),
                "aaaqeayeaudaocajbifqydiob4ibceqtcqkrmfyydenbwha5dypq.b32.i2p",
            ),
        ] {
            let mut expected = vec![5, 1, 0, 3, name.len() as u8];
            expected.extend_from_slice(name.as_bytes());
            expected.extend_from_slice(&8333_u16.to_be_bytes());
            request(Socks5Addr::try_from(address).unwrap(), &expected).await;
        }
        assert!(Socks5Addr::try_from(AddrV2::TorV2([0; 10])).is_err());
        assert!(Socks5Addr::try_from(AddrV2::Unknown(42, vec![1])).is_err());
    }
}

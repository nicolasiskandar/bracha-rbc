FROM rust:1.83-slim AS builder
WORKDIR /app
COPY . .
RUN cargo build --release -p brb-experiments

FROM debian:bookworm-slim
RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates && rm -rf /var/lib/apt/lists/*
COPY --from=builder /app/target/release/brb-experiments /usr/local/bin/
ENTRYPOINT ["brb-experiments"]
CMD ["run", "--scenario", "a", "--seed", "42"]

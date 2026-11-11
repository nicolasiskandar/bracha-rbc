use crate::{
    adversary::{ByzantineProcess, ByzantineStrategy},
    network::SimNetwork,
    scheduler::SchedulePolicy,
};
use brb_core::{Config, InstanceId, Message};
use std::collections::HashSet;

fn instance() -> InstanceId {
    InstanceId(1)
}
fn config_4_1() -> Config {
    Config::new(4, 1)
}
fn value_a() -> Vec<u8> {
    b"value-A".to_vec()
}
fn value_b() -> Vec<u8> {
    b"value-B".to_vec()
}

pub fn scenario_a(seed: u64) -> SimNetwork {
    let byzantine = vec![ByzantineProcess::new(3, ByzantineStrategy::Silent)];
    let mut net = SimNetwork::new(
        vec![0, 1, 2],
        vec![3],
        0,
        config_4_1(),
        instance(),
        SchedulePolicy::Random { seed },
        byzantine,
    );
    net.initiate(0, value_a());
    net
}

pub fn scenario_b(seed: u64) -> SimNetwork {
    let targets_v1: HashSet<u32> = vec![1].into_iter().collect();
    let byzantine = vec![ByzantineProcess::new(
        0,
        ByzantineStrategy::EquivocateInit {
            v1: value_a(),
            v2: value_b(),
            targets_v1,
        },
    )];
    let mut net = SimNetwork::new(
        vec![1, 2, 3],
        vec![0],
        0,
        config_4_1(),
        instance(),
        SchedulePolicy::Random { seed },
        byzantine,
    );
    net.inject_byzantine_messages();
    net
}

pub fn scenario_c(seed: u64) -> SimNetwork {
    let dup_message = Message::Echo {
        instance: instance(),
        value: value_a(),
    };
    let byzantine = vec![ByzantineProcess::new(
        3,
        ByzantineStrategy::DuplicateMessages {
            message: dup_message,
            count: 50,
        },
    )];
    let mut net = SimNetwork::new(
        vec![0, 1, 2],
        vec![3],
        0,
        config_4_1(),
        instance(),
        SchedulePolicy::Random { seed },
        byzantine,
    );
    net.initiate(0, value_a());
    net.inject_byzantine_messages();
    net
}

pub fn scenario_d(seed: u64) -> (SimNetwork, SimNetwork) {
    let side_a: HashSet<u32> = vec![0, 1].into_iter().collect();
    let side_b: HashSet<u32> = vec![2, 3].into_iter().collect();

    let mut partitioned = SimNetwork::new(
        vec![0, 1, 2, 3],
        vec![],
        0,
        Config::new(4, 1),
        instance(),
        SchedulePolicy::Partition { side_a, side_b },
        vec![],
    );
    partitioned.initiate(0, value_a());
    partitioned.run_until_quiescent(100);

    let mut recovered = SimNetwork::new(
        vec![0, 1, 2, 3],
        vec![],
        0,
        Config::new(4, 1),
        instance(),
        SchedulePolicy::Random { seed },
        vec![],
    );
    recovered.honest = partitioned.honest;
    recovered.pending = partitioned.pending;
    recovered.tick = partitioned.tick;
    recovered.deliveries = partitioned.deliveries;
    recovered.trace = partitioned.trace;

    let dummy = SimNetwork::new(
        vec![0, 1, 2, 3],
        vec![],
        0,
        Config::new(4, 1),
        instance(),
        SchedulePolicy::Fifo,
        vec![],
    );
    (dummy, recovered)
}

pub fn scenario_e(seed: u64) -> SimNetwork {
    let targets_v1: HashSet<u32> = vec![0, 1].into_iter().collect();
    let byzantine = vec![ByzantineProcess::new(
        3,
        ByzantineStrategy::EquivocateReady {
            v1: value_a(),
            v2: value_b(),
            targets_v1,
        },
    )];
    let mut net = SimNetwork::new(
        vec![0, 1, 2],
        vec![3],
        0,
        config_4_1(),
        instance(),
        SchedulePolicy::Random { seed },
        byzantine,
    );
    net.initiate(0, value_a());
    net.inject_byzantine_messages();
    net
}

pub fn scenario_a_generic(n: usize, f: usize, seed: u64) -> SimNetwork {
    let config = Config::new(n, f);
    let honest_ids: Vec<u32> = (0..((n - f) as u32)).collect();
    let byz_ids: Vec<u32> = ((n - f) as u32..(n as u32)).collect();

    let byzantine: Vec<ByzantineProcess> = byz_ids
        .iter()
        .map(|&id| ByzantineProcess::new(id, ByzantineStrategy::Silent))
        .collect();

    let mut net = SimNetwork::new(
        honest_ids,
        byz_ids,
        0,
        config,
        instance(),
        SchedulePolicy::Random { seed },
        byzantine,
    );
    net.initiate(0, b"benchmark-value".to_vec());
    net
}

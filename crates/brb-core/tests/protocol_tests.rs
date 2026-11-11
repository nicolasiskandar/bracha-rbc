use brb_core::*;

fn val(s: &str) -> Value {
    s.as_bytes().to_vec()
}

fn make_instance(
    id: u64,
    process_id: ProcessId,
    broadcaster: ProcessId,
    n: usize,
    f: usize,
) -> BroadcastInstance {
    BroadcastInstance::new(InstanceId(id), process_id, broadcaster, Config::new(n, f))
}

fn run_honest_round_4_1(value: &Value) -> Vec<BroadcastInstance> {
    let n = 4usize;
    let f = 1usize;
    let broadcaster = 0u32;

    let mut instances: Vec<BroadcastInstance> = (0..n as u32)
        .map(|id| make_instance(1, id, broadcaster, n, f))
        .collect();

    let init_actions = instances[0].initiate(value.clone());

    let mut pending: Vec<(ProcessId, ProcessId, Message)> = Vec::new();

    for action in &init_actions {
        if let Action::Broadcast(msg) = action {
            for pid in 0..n as u32 {
                if pid != broadcaster {
                    pending.push((broadcaster, pid, msg.clone()));
                }
            }
        }
    }

    let mut max_rounds = 20;
    while !pending.is_empty() && max_rounds > 0 {
        max_rounds -= 1;
        let current = std::mem::take(&mut pending);
        for (from, to, msg) in current {
            let actions = instances[to as usize].handle_message(from, &msg).unwrap();
            for action in actions {
                if let Action::Broadcast(new_msg) = action {
                    for pid in 0..n as u32 {
                        if pid != to {
                            pending.push((to, pid, new_msg.clone()));
                        }
                    }
                }
            }
        }
    }

    instances
}

#[test]
fn test_honest_4_1_full_round() {
    let value = val("hello-world");
    let instances = run_honest_round_4_1(&value);

    for (i, inst) in instances.iter().enumerate() {
        assert_eq!(
            inst.state.delivered,
            Some(value.clone()),
            "process {i} did not deliver"
        );
        assert_eq!(
            inst.state.echo_sent,
            Some(value.clone()),
            "process {i} did not echo"
        );
        assert_eq!(
            inst.state.ready_sent,
            Some(value.clone()),
            "process {i} did not send ready"
        );
    }
}

#[test]
fn test_echo_deduplication() {
    let mut inst = make_instance(1, 1, 0, 4, 1);
    let value = val("dup-test");

    for _ in 0..10 {
        let msg = Message::Echo {
            instance: InstanceId(1),
            value: value.clone(),
        };
        let _ = inst.handle_message(2, &msg);
    }

    assert_eq!(inst.state.echo_count(&value), 1);
}

#[test]
fn test_no_double_echo() {
    let mut inst = make_instance(1, 1, 0, 4, 1);
    let v1 = val("first");
    let v2 = val("second");

    let init1 = Message::Init {
        instance: InstanceId(1),
        value: v1.clone(),
    };
    let actions1 = inst.handle_message(0, &init1).unwrap();
    assert!(actions1
        .iter()
        .any(|a| matches!(a, Action::Broadcast(Message::Echo { .. }))));

    let init2 = Message::Init {
        instance: InstanceId(1),
        value: v2.clone(),
    };
    let actions2 = inst.handle_message(0, &init2).unwrap();
    assert!(actions2.is_empty(), "second INIT should produce no actions");
    assert_eq!(inst.state.echo_sent, Some(v1), "echo_sent must not change");
}

#[test]
fn test_no_double_ready() {
    let mut inst = make_instance(1, 1, 0, 4, 1);
    let v1 = val("value-a");
    let v2 = val("value-b");

    let _ = inst.handle_message(
        0,
        &Message::Init {
            instance: InstanceId(1),
            value: v1.clone(),
        },
    );

    let _ = inst.handle_message(
        2,
        &Message::Echo {
            instance: InstanceId(1),
            value: v1.clone(),
        },
    );
    let _ = inst.handle_message(
        3,
        &Message::Echo {
            instance: InstanceId(1),
            value: v1.clone(),
        },
    );

    assert_eq!(inst.state.ready_sent, Some(v1.clone()));

    let _ = inst.handle_message(
        2,
        &Message::Ready {
            instance: InstanceId(1),
            value: v2.clone(),
        },
    );
    let _ = inst.handle_message(
        3,
        &Message::Ready {
            instance: InstanceId(1),
            value: v2.clone(),
        },
    );

    assert_eq!(
        inst.state.ready_sent,
        Some(v1),
        "ready_sent must not change to a different value"
    );
}

#[test]
fn test_no_double_deliver() {
    let value = val("deliver-once");
    let instances = run_honest_round_4_1(&value);

    for inst in &instances {
        assert_eq!(inst.state.delivered, Some(value.clone()));
    }
}

#[test]
fn test_wrong_instance_rejected() {
    let mut inst = make_instance(1, 1, 0, 4, 1);
    let msg = Message::Echo {
        instance: InstanceId(999),
        value: val("wrong"),
    };
    let result = inst.handle_message(2, &msg);
    assert!(matches!(result, Err(ProtocolError::WrongInstance { .. })));
}

#[test]
fn test_init_from_non_broadcaster_rejected() {
    let mut inst = make_instance(1, 1, 0, 4, 1);
    let msg = Message::Init {
        instance: InstanceId(1),
        value: val("fake-init"),
    };

    let result = inst.handle_message(2, &msg);
    assert!(matches!(
        result,
        Err(ProtocolError::InitFromNonBroadcaster { .. })
    ));
}

#[test]
fn test_malformed_empty_value() {
    let mut inst = make_instance(1, 1, 0, 4, 1);
    let msg = Message::Echo {
        instance: InstanceId(1),
        value: vec![],
    };
    let result = inst.handle_message(2, &msg);
    assert!(matches!(result, Err(ProtocolError::Malformed)));
}

#[test]
fn test_n7_f2() {
    let n = 7usize;
    let f = 2usize;
    let broadcaster = 0u32;
    let value = val("seven-nodes");

    let mut instances: Vec<BroadcastInstance> = (0..n as u32)
        .map(|id| make_instance(1, id, broadcaster, n, f))
        .collect();

    let init_actions = instances[0].initiate(value.clone());
    let mut pending: Vec<(ProcessId, ProcessId, Message)> = Vec::new();

    for action in &init_actions {
        if let Action::Broadcast(msg) = action {
            for pid in 0..n as u32 {
                if pid != broadcaster {
                    pending.push((broadcaster, pid, msg.clone()));
                }
            }
        }
    }

    let mut max_rounds = 30;
    while !pending.is_empty() && max_rounds > 0 {
        max_rounds -= 1;
        let current = std::mem::take(&mut pending);
        for (from, to, msg) in current {
            let actions = instances[to as usize].handle_message(from, &msg).unwrap();
            for action in actions {
                if let Action::Broadcast(new_msg) = action {
                    for pid in 0..n as u32 {
                        if pid != to {
                            pending.push((to, pid, new_msg.clone()));
                        }
                    }
                }
            }
        }
    }

    for (i, inst) in instances.iter().enumerate() {
        assert_eq!(
            inst.state.delivered,
            Some(value.clone()),
            "process {i} did not deliver in n=7 f=2"
        );
    }
}

#[test]
fn test_ready_amplification() {
    let mut inst = make_instance(1, 1, 0, 4, 1);
    let value = val("amplify");

    let _ = inst.handle_message(
        2,
        &Message::Ready {
            instance: InstanceId(1),
            value: value.clone(),
        },
    );

    assert!(
        inst.state.ready_sent.is_none(),
        "f+1=2 not yet reached after 1 READY"
    );

    let actions = inst
        .handle_message(
            3,
            &Message::Ready {
                instance: InstanceId(1),
                value: value.clone(),
            },
        )
        .unwrap();

    assert_eq!(inst.state.ready_sent, Some(value.clone()));
    assert!(
        actions
            .iter()
            .any(|a| matches!(a, Action::Broadcast(Message::Ready { .. }))),
        "amplification should broadcast READY"
    );
}

#[test]
fn test_instance_isolation() {
    let value = val("instance-test");

    let mut inst_a = make_instance(1, 1, 0, 4, 1);
    let mut inst_b = make_instance(2, 1, 0, 4, 1);

    let _ = inst_a.handle_message(
        0,
        &Message::Init {
            instance: InstanceId(1),
            value: value.clone(),
        },
    );

    let result = inst_b.handle_message(
        0,
        &Message::Init {
            instance: InstanceId(1),
            value: value.clone(),
        },
    );
    assert!(matches!(result, Err(ProtocolError::WrongInstance { .. })));

    assert!(inst_b.state.echo_sent.is_none());
}

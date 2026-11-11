use brb_core::*;

#[test]
fn test_config_boundary_values() {
    assert!(Config::try_new(4, 1).is_ok());
    assert!(Config::try_new(7, 2).is_ok());
    assert!(Config::try_new(10, 3).is_ok());
    assert!(Config::try_new(13, 4).is_ok());
    assert!(Config::try_new(3, 1).is_err());
    assert!(Config::try_new(6, 2).is_err());
    assert!(Config::try_new(1, 0).is_ok());
}

#[test]
fn test_multiple_values_echo_tracking() {
    let mut inst = BroadcastInstance::new(InstanceId(1), 1, 0, Config::new(4, 1));
    let v1 = b"val-1".to_vec();
    let v2 = b"val-2".to_vec();

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
            value: v2.clone(),
        },
    );

    assert_eq!(inst.state.echo_count(&v1), 1);
    assert_eq!(inst.state.echo_count(&v2), 1);

    assert!(inst.state.ready_sent.is_none());
}

#[test]
fn test_ready_before_echo() {
    let mut inst = BroadcastInstance::new(InstanceId(1), 1, 0, Config::new(4, 1));
    let value = b"ready-first".to_vec();

    let _ = inst.handle_message(
        2,
        &Message::Ready {
            instance: InstanceId(1),
            value: value.clone(),
        },
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
    assert!(actions
        .iter()
        .any(|a| matches!(a, Action::Broadcast(Message::Ready { .. }))));
}

#[test]
fn test_large_value() {
    let mut inst = BroadcastInstance::new(InstanceId(1), 1, 0, Config::new(4, 1));
    let big_value: Vec<u8> = (0..10_000u32).map(|i| (i % 256) as u8).collect();

    let result = inst.handle_message(
        0,
        &Message::Init {
            instance: InstanceId(1),
            value: big_value.clone(),
        },
    );
    assert!(result.is_ok());
    assert_eq!(inst.state.echo_sent, Some(big_value));
}

#[test]
fn test_ready_deduplication() {
    let mut inst = BroadcastInstance::new(InstanceId(1), 1, 0, Config::new(4, 1));
    let value = b"dup-ready".to_vec();

    for _ in 0..20 {
        let _ = inst.handle_message(
            2,
            &Message::Ready {
                instance: InstanceId(1),
                value: value.clone(),
            },
        );
    }
    assert_eq!(inst.state.ready_count(&value), 1);
}

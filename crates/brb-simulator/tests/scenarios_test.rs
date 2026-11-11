use brb_simulator::scenarios;

#[test]
fn test_scenario_a_100_seeds() {
    for seed in 0..100u64 {
        let mut net = scenarios::scenario_a(seed);
        net.run_until_quiescent(1000);
        assert!(net.safety_holds(), "safety violated seed={seed}");
        assert_eq!(
            net.deliveries.len(),
            3,
            "not all correct nodes delivered seed={seed}"
        );

        let vals = net.delivered_values();
        let expected = b"value-A".to_vec();
        for (&pid, val) in &vals {
            assert_eq!(val, &expected, "wrong value at pid={pid} seed={seed}");
        }
    }
}

#[test]
fn test_scenario_b_100_seeds() {
    for seed in 0..100u64 {
        let mut net = scenarios::scenario_b(seed);
        net.run_until_quiescent(1000);
        assert!(net.safety_holds(), "safety violated seed={seed}");
    }
}

#[test]
fn test_scenario_c_100_seeds() {
    for seed in 0..100u64 {
        let mut net = scenarios::scenario_c(seed);
        net.run_until_quiescent(1000);
        assert!(net.safety_holds(), "safety violated seed={seed}");

        assert!(net.deliveries.len() >= 3, "delivery failed seed={seed}");
    }
}

#[test]
fn test_scenario_d_100_seeds() {
    for seed in 0..100u64 {
        let (_, mut recovered) = scenarios::scenario_d(seed);

        recovered.run_until_quiescent(1000);
        assert!(
            recovered.safety_holds(),
            "safety violated after recovery seed={seed}"
        );
    }
}

#[test]
fn test_scenario_e_100_seeds() {
    for seed in 0..100u64 {
        let mut net = scenarios::scenario_e(seed);
        net.run_until_quiescent(1000);
        assert!(net.safety_holds(), "safety violated seed={seed}");
    }
}

#[test]
fn test_generic_7_2() {
    for seed in 0..50u64 {
        let mut net = scenarios::scenario_a_generic(7, 2, seed);
        net.run_until_quiescent(5000);
        assert!(net.safety_holds(), "safety violated n=7 seed={seed}");
        assert_eq!(
            net.deliveries.len(),
            5,
            "not all correct delivered n=7 seed={seed}"
        );
    }
}

#[test]
fn test_generic_10_3() {
    for seed in 0..20u64 {
        let mut net = scenarios::scenario_a_generic(10, 3, seed);
        net.run_until_quiescent(5000);
        assert!(net.safety_holds(), "safety violated n=10 seed={seed}");
        assert_eq!(
            net.deliveries.len(),
            7,
            "not all correct delivered n=10 seed={seed}"
        );
    }
}

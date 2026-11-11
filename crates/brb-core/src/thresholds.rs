#[derive(Clone, Copy, Debug)]
pub struct Config {
    pub n: usize,

    pub f: usize,
}

impl Config {
    pub fn new(n: usize, f: usize) -> Self {
        assert!(
            n > 3 * f,
            "Byzantine bound violated: n={n} must be > 3*f={}",
            3 * f
        );
        Config { n, f }
    }

    pub fn try_new(n: usize, f: usize) -> Result<Self, String> {
        if n > 3 * f {
            Ok(Config { n, f })
        } else {
            Err(format!(
                "Byzantine bound violated: n={n} must be > 3*f={}",
                3 * f
            ))
        }
    }

    pub fn echo_threshold(&self) -> usize {
        self.n - self.f
    }

    pub fn ready_amplify_threshold(&self) -> usize {
        self.f + 1
    }

    pub fn deliver_threshold(&self) -> usize {
        self.n - self.f
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_config_4_1() {
        let c = Config::new(4, 1);
        assert_eq!(c.echo_threshold(), 3);
        assert_eq!(c.ready_amplify_threshold(), 2);
        assert_eq!(c.deliver_threshold(), 3);
    }

    #[test]
    fn test_config_7_2() {
        let c = Config::new(7, 2);
        assert_eq!(c.echo_threshold(), 5);
        assert_eq!(c.ready_amplify_threshold(), 3);
        assert_eq!(c.deliver_threshold(), 5);
    }

    #[test]
    #[should_panic(expected = "Byzantine bound violated")]
    fn test_invalid_config() {
        Config::new(3, 1);
    }

    #[test]
    fn test_try_new_invalid() {
        assert!(Config::try_new(3, 1).is_err());
        assert!(Config::try_new(4, 1).is_ok());
    }
}

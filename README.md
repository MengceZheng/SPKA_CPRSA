# Revisiting Small Private Key Attacks on Common Prime RSA

## Introduction

This is a Python implementation of lattice-based attack proposed in **Revisiting Small Private Key Attacks on Common Prime RSA**[^SPKACPRSA]. Some underlying functions are based on [Joachim Vandersmissen&#39;s crypto-attacks](https://github.com/jvdsn/crypto-attacks) and some ideas are inspired from [Yansong Feng](https://github.com/fffmath).

## Requirements

- [**SageMath**](https://www.sagemath.org/) 9.5 with Python 3.10

You can check your SageMath Python version using the following command:

```commandline
$ sage -python --version
Python 3.10.12
```

Note: If your SageMath Python version is older than 3.9.0, some features in given scripts might not work.

## Usage

The standard way to run the attack with the specific parameters $\ell$, $\gamma$, $\delta$, and $s$ requires passing them as command line arguments `sage -python attack.py <modulus_bit_length> <gamma> <delta> <s>`. For instance, to run the attack with $\ell=256$, $\gamma=0.3$, $\delta=0.14$, and $s=2$, please run `sage -python attack.py 256 0.3 0.14 2`:

```commandline
SPKA_CPRSA$ sage -python attack.py 256 0.3 0.14 2
The parameters: N = 63236039457260578412497711927910293735878673126804182969089706148653918249935 and e = 145739672445113948849846979314050302144141498062509003
Found primes: 223562247299154966144036511511089027139 and 282856520817858148936977711952759948165
The attack costs 0.538 seconds...
```

For instance, to run the attack with $\ell=256$, $\gamma=0.4$, $\delta=0.18$, and $s=3$, please run `sage -python attack.py 256 0.4 0.18 3`:

```commandline
SPKA_CPRSA$ sage -python attack.py 256 0.4 0.18 3
The parameters: N = 86979996154219372057125079917167888635328352326366555664505555588514924260695 and e = 4352284220734458151939458402045072251879045639
Found primes: 290119823470188643798682482670924661955 and 299807145591886897263554557316564900829
The attack costs 11.433 seconds...
```

For instance, to run the attack with $\ell=256$, $\gamma=0.45$, $\delta=0.2$, and $s=3$, please run `sage -python attack.py 256 0.45 0.2 3`:

```commandline
SPKA_CPRSA$ sage -python attack.py 256 0.45 0.2 3
The parameters: N = 61552569346213811735143034171114001039568008154180313065484412227486057176075 and e = 223190992838379235483530540382096126794459
Found primes: 221089799980331833665016302538931380589 and 278405287587620655679073975374948057175
The attack costs 12.562 seconds...
```

## Notes

All the details of the numerical attack experiments are recorded in the `attack.log` file.

[^SPKACPRSA]: Zheng M., "Revisiting Small Private Key Attacks on Common Prime RSA" | [PDF](https://mengcezheng.github.io/assets/files/Zheng24.pdf)

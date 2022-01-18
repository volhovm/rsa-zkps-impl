use curv::BigInt;
use itertools::Itertools;
use paillier::*;
use rand::distributions::{Distribution, Uniform};
use rand::seq::SliceRandom;
use rand::thread_rng;
use std::collections::HashSet;
use std::hash::Hash;
use std::sync::atomic::{AtomicU64,Ordering};
use std::sync::{Arc, Mutex};
use std::thread;
use zk_paillier::zkproofs::{CiphertextProof,CiphertextWitness,CiphertextStatement};


fn test_lemma() {
//    let gen = Uniform::from(0..(2 * (params.lambda as usize)));

    for lambda in [10,20,30,40] {
        let m = lambda; // should be < 2*lambda
        let two_lambda = 1 << lambda;
        let attempts1 = 100;
        let attempts2 = 5000;
        let cores = 4;


        let counter = Arc::new(AtomicU64::new(0));
        //let counter = Arc::new(Mutex::new(0));
        //let mut counter = Arc::new(atomic_counter::ConsistentCounter::new(0));
        //let mut counterLink = &counter;


        for _i in 0..(attempts1/cores) {
            let mut handles = vec![];
            for _i in 0..cores {
                let counter = Arc::clone(&counter);
                let handle = thread::spawn(move || {
                    // I hope this gives different randomness per thread
                    let mut rng = rand::thread_rng();

                    //let mut dx = vec![0; 2*lambda];
                    let mut dx: Vec<i128> = vec![0;2*lambda];
                    let mut dprimex: Vec<i128> = vec![0;lambda];
                    let mut jx: Vec<i128> = vec![0;m-1];

                    for j in 0..2*lambda {
                        let v: i128 = Uniform::from(-two_lambda..two_lambda).sample(&mut rng);
                        dx[j] = v;
                    }
                    for _i in 0..attempts2 {
                        for j in 0..lambda {
                            dx.shuffle(&mut rng);
                            dprimex[j] = 0;
                            for i in 0..lambda {
                                dprimex[j] += dx[i];
                            }
                        }
                        for j in 0..m-1 {
                            jx[j] = dprimex[j+1] - dprimex[0];
                        }
                        //println!("Numbers: {:?}",jx);

                        for i in 1..m-1 {
                            jx[0] = num::integer::gcd::<i128>(jx[0],jx[i]);
                        }

                        if jx[0] != 1 {
                            counter.fetch_add(1, Ordering::SeqCst);
                            //atomic_counter::AtomicCounter::inc(counter);
//                            let mut num = counter.lock().unwrap();
//                            *num += 1;
                        }
                    }
                });
                handles.push(handle)
            }

            for handle in handles {
                handle.join().unwrap();
            }
            //println!("Number of nonzero: {:?}/{:?}",count,attempts2);
        }
        println!("lambda = {:?}, m = {:?}: {:?}/{:?}",lambda,m,counter,attempts1*attempts2);
    }
}

fn has_unique_elements<T>(iter: T) -> bool
where
    T: IntoIterator,
    T::Item: Eq + Hash,
{
    let mut uniq = HashSet::new();
    iter.into_iter().all(move |x| uniq.insert(x))
}

fn test_lemma_q_div() {
    for lambda in [10] {
    for q in [7,11,13,19,23,31,47,67] {
//    for q in [5] {
        let m = lambda;
        let two_lambda = 1 << lambda;
        let attempts1 = 100;
        let attempts2 = 10000;
        let cores = 4;

        let counter = Arc::new(AtomicU64::new(0));

        let mut handles = vec![];
        for _i in 0..cores {
            let counter = Arc::clone(&counter);
            let handle = thread::spawn(move || {
                // I hope this gives different randomness per thread
                let mut rng = rand::thread_rng();

                for _i in 0..(attempts1/cores) {
                    //let mut dx = vec![0; 2*lambda];
                    let mut dx: Vec<i128> = vec![0;2*lambda];

                    while !has_unique_elements(dx.iter()) {
                        for j in 0..2*lambda {
                            dx[j] = Uniform::from(-two_lambda..two_lambda).sample(&mut rng);
                        }
                    }
                    //println!("dx: {:?}",dx);

                    for _i in 0..attempts2 {
                        let mut dprimex: Vec<i128> = vec![0;lambda];
                        let mut jx: Vec<i128> = vec![0;m-1];
                        while !has_unique_elements(dprimex.iter()) {
                            for j in 0..lambda {
                                dx.shuffle(&mut rng);
                                dprimex[j] = 0;
                                for i in 0..lambda {
                                    dprimex[j] += dx[i];
                                }
                            }
                        }
                        //println!("dprimex: {:?}",dprimex);

                        //for j in 0..m-1 {
                        //    jx[j] = dprimex[j+1] - dprimex[0];
                        //}

                        let mut divall = true;
                        for i in 0..m-1 {
                            if !divall { break; }
                            divall = divall && (dprimex[i] % q == 0);
                        }

                        if divall { counter.fetch_add(1, Ordering::SeqCst); }
                    }
                }
            });
            handles.push(handle)
        }

        for handle in handles {
            handle.join().unwrap();
        }

        let v = counter.load(Ordering::SeqCst);
        println!("q = {:?}, lambda = {:?}, m = {:?}: {:?}/{:?} => 1/Pr = {:?}; q^(m-1) = {:?}",
                 q,lambda,m,v,attempts1*attempts2,
                 if v == 0 { 0 } else {attempts1*attempts2 / v}, q.pow((m-1) as u32));
    }}
}


fn fact(num: u64) -> u64 {
    return if num == 1 { 1 } else { num * fact(num - 1) }
}

fn test_lemma_q_div_bruteforce() {
    for lambda in [4] {
        let q = 2;
        let m = lambda;
        let two_lambda = 1 << lambda;
        //let cores = 4;

//        let allcomb_len = fact(2*lambda) / (2*fact(lambda));
//        let all_len = fact(allcomb_len) / (fact(lambda) * fact(allcomb_len-lambda));
//        println!("Length: {:?}, {:?}", allcomb_len, all_len);

        let mut rng = rand::thread_rng();

        let mut dx: Vec<i128> = vec![0;2*lambda];
        for j in 0..2*lambda {
            dx[j] = Uniform::from(-two_lambda..two_lambda).sample(&mut rng);
        }

        let mut allcomb: Vec<i128> = Vec::new();
        for comb in dx.iter().combinations(lambda) {
            let mut x = 0;
            for i in 0..lambda { x += comb[i]; }
            allcomb.push(x);
        }

        let mut counter: u64 = 0;
        for comb in allcomb.iter().combinations(lambda) {
            let mut divall = true;
            for i in 0..m-1 {
                if !divall { break; }
                divall = divall && (comb[i] % q == 0);
            }
            if divall { counter += 1; }
        }

        println!("q = {:?}, lambda = {:?}, m = {:?}: {:?} ",
                 q,lambda,m,counter);
    }
}




fn _check_correct_ciphertext_proof() {
    let kp:Keypair = Paillier::keypair();
    let (pk,_) = kp.keys();

    let m = BigInt::from(1u32);
    let r = BigInt::from(2u32);

    let ct = Paillier::encrypt_with_chosen_randomness(
             &pk,
             RawPlaintext::from(m.clone()),
             &Randomness(r.clone())).0.into_owned();

    let w = CiphertextWitness{ x: m.clone(), r: r };
    let w_false = CiphertextWitness{x:m,r:BigInt::from(3)};
    let x = CiphertextStatement{ ek: pk, c: ct };

    let res1 = CiphertextProof::prove(&w,&x).verify(&x);
    println!("Honest proof verifies: {:?}", res1);

    let res2 = CiphertextProof::prove(&w_false,&x).verify(&x);
    println!("Bogus proof verification gives: {:?}", res2);
}

fn main() {
    //test_lemma();
    test_lemma_q_div();
    //test_lemma_q_div_bruteforce();
//    rsazkps::protocols::snark_paillier::test();
//    rsazkps::protocols::schnorr_paillier_batched::tests::test_correctness();
}

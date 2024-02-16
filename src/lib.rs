use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError, ConstraintSystem};

use ark_crypto_primitives::crh::{pedersen, TwoToOneCRHScheme, TwoToOneCRHSchemeGadget};

use ark_crypto_primitives::crh::{CRHScheme, CRHSchemeGadget};
use ark_crypto_primitives::merkle_tree::constraints::{BytesVarDigestConverter, ConfigGadget};
use ark_crypto_primitives::merkle_tree::{LeafParam, TwoToOneParam, constraints::PathVar, ByteDigestConverter, Config, MerkleTree, Path, DigestConverter};
use ark_crypto_primitives::snark::SNARK;
use ark_ed_on_bls12_381::{constraints::EdwardsVar, EdwardsProjective as JubJub, Fq};
use ark_r1cs_std::prelude::*;
use ark_std::{cfg_into_iter, cfg_iter_mut, rand::{prelude::StdRng, SeedableRng}};
#[allow(unused_imports)]
#[macro_use]
extern crate derivative;
use ark_bls12_381::{Bls12_381, Fr};

#[derive(Clone)]
pub struct Window4x256;
impl pedersen::Window for Window4x256 {
    const WINDOW_SIZE: usize = 4;
    const NUM_WINDOWS: usize = 256;
}

type LeafH = pedersen::CRH<JubJub, Window4x256>;
type LeafHG = pedersen::constraints::CRHGadget<JubJub, EdwardsVar, Window4x256>;

type CompressH = pedersen::TwoToOneCRH<JubJub, Window4x256>;
type CompressHG = pedersen::constraints::TwoToOneCRHGadget<JubJub, EdwardsVar, Window4x256>;

type LeafVar<ConstraintF> = [UInt8<ConstraintF>];

#[derive(Derivative)]
#[derivative(Clone(bound = "P: Config"))]
pub struct MC<P: Config> {
    // leaf
    leaf: Option<Vec<u8>>,
    /// root
    root: Option<P::LeafDigest>,
    /// Store the inner hash parameters
    two_to_one_hash_param: TwoToOneParam<P>,
    /// Store the leaf hash parameters
    leaf_hash_param: LeafParam<P>,
    // /// Stores the height of the MerkleTree
    // height: usize,
    /// proof
    proof: Option<Path<P>>,
}

impl<P: Config> MC<P> {
    /// Create an empty merkle tree such that all leaves are zero-filled.
    /// Consider using a sparse merkle tree if you need the tree to be low memory
    pub fn blank(
        leaf_hash_param: &LeafParam<P>,
        two_to_one_hash_param: &TwoToOneParam<P>,
    ) -> Result<Self, ark_crypto_primitives::Error> {
        Ok(MC {
            leaf: None,
            root: None,
            two_to_one_hash_param: two_to_one_hash_param.clone(),
            leaf_hash_param: leaf_hash_param.clone(),
            proof: None,
        })
    }

    /// Returns a new merkle tree. `leaves.len()` should be power of two.
    pub fn new(
        leaf_hash_param: &LeafParam<P>,
        two_to_one_hash_param: &TwoToOneParam<P>,
        leaf: Vec<u8>,
        root: P::LeafDigest,
        proof: Path<P>
    ) -> Result<Self, ark_crypto_primitives::Error> {
        Ok(MC {
            leaf: Some(leaf),
            root: Some(root),
            leaf_hash_param: leaf_hash_param.clone(),
            two_to_one_hash_param: two_to_one_hash_param.clone(),
            proof: Some(proof),
        })
    }
}

type JubJubMerkleTreeCircuit = MC<JubJubMerkleTreeParams>;

impl ConstraintSynthesizer<ConstraintF> for JubJubMerkleTreeCircuit {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<ConstraintF>,
    ) -> Result<(), SynthesisError> {

        // Allocate Merkle Tree Root
        let root = <LeafHG as CRHSchemeGadget<LeafH, _>>::OutputVar::new_witness(
            ark_relations::ns!(cs, "new_digest"),
            || {
                self.root.ok_or(SynthesisError::AssignmentMissing)
            },
        )
            .unwrap();

        let leaf_g = UInt8::new_witness_vec(cs.clone(), &self.leaf.ok_or(SynthesisError::AssignmentMissing).unwrap()).unwrap();

        // Allocate Parameters for CRH
        let leaf_crh_params_var =
            <LeafHG as CRHSchemeGadget<LeafH, _>>::ParametersVar::new_constant(
                ark_relations::ns!(cs, "leaf_crh_parameter"),
                &self.leaf_hash_param,// leaf_crh_params,
            )
                .unwrap();
        let two_to_one_crh_params_var =
            <CompressHG as TwoToOneCRHSchemeGadget<CompressH, _>>::ParametersVar::new_constant(
                ark_relations::ns!(cs, "two_to_one_crh_parameter"),
                &self.two_to_one_hash_param, // two_to_one_crh_params,
            )
                .unwrap();

        // Allocate Merkle Tree Path
        let proof = self.proof.unwrap();
        let cw: PathVar<JubJubMerkleTreeParams, Fq, JubJubMerkleTreeParamsVar> =
            PathVar::new_witness(ark_relations::ns!(cs, "new_witness"), || Ok(proof)).unwrap();

        // Now, we have to check membership. How do we do that?
        // Hint: look at https://github.com/arkworks-rs/crypto-primitives/blob/6be606259eab0aec010015e2cfd45e4f134cd9bf/src/merkle_tree/constraints.rs#L135

        let is_member = cw. verify_membership(
            &leaf_crh_params_var,
            &two_to_one_crh_params_var,
            &root,
            &leaf_g,
        )
            .unwrap();

        is_member.enforce_equal(&Boolean::TRUE)?;

        Ok(())
    }
}

#[derive(Derivative)]
#[derivative(Clone(bound = "P: Config"))]
pub struct MT<P: Config> {
    // /// stores the non-leaf nodes in level order. The first element is the root node.
    // /// The ith nodes (starting at 1st) children are at indices `2*i`, `2*i+1`
    non_leaf_nodes: Vec<P::InnerDigest>,
    /// store the hash of leaf nodes from left to right
    leaf_nodes: Vec<P::LeafDigest>,
    /// Store the inner hash parameters
    two_to_one_hash_param: TwoToOneParam<P>,
    /// Store the leaf hash parameters
    leaf_hash_param: LeafParam<P>,
    /// Stores the height of the MerkleTree
    height: usize,
    /// proof
    proof: Option<Path<P>>,
}

impl<P: Config> MT<P> {
    /// Create an empty merkle tree such that all leaves are zero-filled.
    /// Consider using a sparse merkle tree if you need the tree to be low memory
    pub fn blank(
        leaf_hash_param: &LeafParam<P>,
        two_to_one_hash_param: &TwoToOneParam<P>,
        height: usize,
    ) -> Result<Self, ark_crypto_primitives::Error> {
        // use empty leaf digest
        let leaf_digests = vec![P::LeafDigest::default(); 1 << (height - 1)];
        Self::new_with_leaf_digest(leaf_hash_param, two_to_one_hash_param, leaf_digests)
    }

    /// Returns a new merkle tree. `leaves.len()` should be power of two.
    pub fn new<L: AsRef<P::Leaf> + Send>(
        leaf_hash_param: &LeafParam<P>,
        two_to_one_hash_param: &TwoToOneParam<P>,
        leaves: impl IntoIterator<Item=L>,
        // #[cfg(feature = "parallel")] leaves: impl IntoParallelIterator<Item=L>,
    ) -> Result<Self, ark_crypto_primitives::Error> {
        let leaf_digests: Vec<_> = cfg_into_iter!(leaves)
            .map(|input| P::LeafHash::evaluate(leaf_hash_param, input.as_ref()))
            .collect::<Result<Vec<_>, _>>()?;

        Self::new_with_leaf_digest(leaf_hash_param, two_to_one_hash_param, leaf_digests)
    }

    pub fn new_with_leaf_digest(
        leaf_hash_param: &LeafParam<P>,
        two_to_one_hash_param: &TwoToOneParam<P>,
        leaf_digests: Vec<P::LeafDigest>,
    ) -> Result<Self, ark_crypto_primitives::Error> {
        let leaf_nodes_size = leaf_digests.len();
        assert!(
            leaf_nodes_size.is_power_of_two() && leaf_nodes_size > 1,
            "`leaves.len() should be power of two and greater than one"
        );
        let non_leaf_nodes_size = leaf_nodes_size - 1;

        let tree_height = tree_height(leaf_nodes_size);

        let hash_of_empty: P::InnerDigest = P::InnerDigest::default();

        // initialize the merkle tree as array of nodes in level order
        let mut non_leaf_nodes: Vec<P::InnerDigest> = cfg_into_iter!(0..non_leaf_nodes_size)
            .map(|_| hash_of_empty.clone())
            .collect();

        // Compute the starting indices for each non-leaf level of the tree
        let mut index = 0;
        let mut level_indices = Vec::with_capacity(tree_height - 1);
        for _ in 0..(tree_height - 1) {
            level_indices.push(index);
            index = left_child(index);
        }

        // compute the hash values for the non-leaf bottom layer
        {
            let start_index = level_indices.pop().unwrap();
            let upper_bound = left_child(start_index);

            cfg_iter_mut!(non_leaf_nodes[start_index..upper_bound])
                .enumerate()
                .try_for_each(|(i, n)| {
                    // `left_child(current_index)` and `right_child(current_index) returns the position of
                    // leaf in the whole tree (represented as a list in level order). We need to shift it
                    // by `-upper_bound` to get the index in `leaf_nodes` list.

                    //similarly, we need to rescale i by start_index
                    //to get the index outside the slice and in the level-ordered list of nodes

                    let current_index = i + start_index;
                    let left_leaf_index = left_child(current_index) - upper_bound;
                    let right_leaf_index = right_child(current_index) - upper_bound;

                    *n = P::TwoToOneHash::evaluate(
                        two_to_one_hash_param,
                        P::LeafInnerDigestConverter::convert(
                            leaf_digests[left_leaf_index].clone(),
                        )?,
                        P::LeafInnerDigestConverter::convert(
                            leaf_digests[right_leaf_index].clone(),
                        )?,
                    )?;
                    Ok::<(), ark_crypto_primitives::Error>(())
                })?;
        }

        // compute the hash values for nodes in every other layer in the tree
        level_indices.reverse();
        for &start_index in &level_indices {
            // The layer beginning `start_index` ends at `upper_bound` (exclusive).
            let upper_bound = left_child(start_index);

            let (nodes_at_level, nodes_at_prev_level) =
                non_leaf_nodes[..].split_at_mut(upper_bound);
            // Iterate over the nodes at the current level, and compute the hash of each node
            cfg_iter_mut!(nodes_at_level[start_index..])
                .enumerate()
                .try_for_each(|(i, n)| {
                    // `left_child(current_index)` and `right_child(current_index) returns the position of
                    // leaf in the whole tree (represented as a list in level order). We need to shift it
                    // by `-upper_bound` to get the index in `leaf_nodes` list.

                    //similarly, we need to rescale i by start_index
                    //to get the index outside the slice and in the level-ordered list of nodes
                    let current_index = i + start_index;
                    let left_leaf_index = left_child(current_index) - upper_bound;
                    let right_leaf_index = right_child(current_index) - upper_bound;

                    // need for unwrap as Box<Error> does not implement trait Send
                    *n = P::TwoToOneHash::compress(
                        two_to_one_hash_param,
                        nodes_at_prev_level[left_leaf_index].clone(),
                        nodes_at_prev_level[right_leaf_index].clone(),
                    )?;
                    Ok::<_, ark_crypto_primitives::Error>(())
                })?;
        }
        Ok(MT {
            leaf_nodes: leaf_digests,
            non_leaf_nodes,
            height: tree_height,
            leaf_hash_param: leaf_hash_param.clone(),
            two_to_one_hash_param: two_to_one_hash_param.clone(),
            proof: None,
        })
    }

    /// Returns the root of the Merkle tree.
    pub fn root(&self) -> P::InnerDigest {
        self.non_leaf_nodes[0].clone()
    }

    /// Returns the height of the Merkle tree.
    pub fn height(&self) -> usize {
        self.height
    }

    /// Returns the authentication path from leaf at `index` to root.
    pub fn generate_proof(&self, index: usize) -> Result<Path<P>, ark_crypto_primitives::Error> {
        // gather basic tree information
        let tree_height = tree_height(self.leaf_nodes.len());

        // Get Leaf hash, and leaf sibling hash,
        let leaf_index_in_tree = convert_index_to_last_level(index, tree_height);
        let leaf_sibling_hash = if index & 1 == 0 {
            // leaf is left child
            self.leaf_nodes[index + 1].clone()
        } else {
            // leaf is right child
            self.leaf_nodes[index - 1].clone()
        };

        // path.len() = `tree height - 2`, the two missing elements being the leaf sibling hash and the root
        let mut path = Vec::with_capacity(tree_height - 2);
        // Iterate from the bottom layer after the leaves, to the top, storing all sibling node's hash values.
        let mut current_node = parent(leaf_index_in_tree).unwrap();
        while !is_root(current_node) {
            let sibling_node = sibling(current_node).unwrap();
            path.push(self.non_leaf_nodes[sibling_node].clone());
            current_node = parent(current_node).unwrap();
        }

        debug_assert_eq!(path.len(), tree_height - 2);

        // we want to make path from root to bottom
        path.reverse();

        Ok(Path {
            leaf_index: index,
            auth_path: path,
            leaf_sibling_hash,
        })
    }


}
/// Returns the height of the tree, given the number of leaves.
#[inline]
fn tree_height(num_leaves: usize) -> usize {
    if num_leaves == 1 {
        return 1;
    }

    (ark_std::log2(num_leaves) as usize) + 1
}
/// Returns true iff the index represents the root.
#[inline]
fn is_root(index: usize) -> bool {
    index == 0
}

/// Returns the index of the left child, given an index.
#[inline]
fn left_child(index: usize) -> usize {
    2 * index + 1
}

/// Returns the index of the right child, given an index.
#[inline]
fn right_child(index: usize) -> usize {
    2 * index + 2
}

/// Returns the index of the sibling, given an index.
#[inline]
fn sibling(index: usize) -> Option<usize> {
    if index == 0 {
        None
    } else if is_left_child(index) {
        Some(index + 1)
    } else {
        Some(index - 1)
    }
}

/// Returns true iff the given index represents a left child.
#[inline]
fn is_left_child(index: usize) -> bool {
    index % 2 == 1
}

/// Returns the index of the parent, given an index.
#[inline]
fn parent(index: usize) -> Option<usize> {
    if index > 0 {
        Some((index - 1) >> 1)
    } else {
        None
    }
}

#[inline]
fn convert_index_to_last_level(index: usize, tree_height: usize) -> usize {
    index + (1 << (tree_height - 1)) - 1
}


struct JubJubMerkleTreeParams;

impl Config for JubJubMerkleTreeParams {
    type Leaf = [u8];
    type LeafDigest = <LeafH as CRHScheme>::Output;
    type LeafInnerDigestConverter = ByteDigestConverter<Self::LeafDigest>;

    type InnerDigest = <CompressH as TwoToOneCRHScheme>::Output;
    type LeafHash = LeafH;
    type TwoToOneHash = CompressH;
}

type ConstraintF = Fq;
struct JubJubMerkleTreeParamsVar;
impl ConfigGadget<JubJubMerkleTreeParams, ConstraintF> for JubJubMerkleTreeParamsVar {
    type Leaf = LeafVar<ConstraintF>;
    type LeafDigest = <LeafHG as CRHSchemeGadget<LeafH, ConstraintF>>::OutputVar;
    type LeafInnerConverter = BytesVarDigestConverter<Self::LeafDigest, ConstraintF>;
    type InnerDigest =
    <CompressHG as TwoToOneCRHSchemeGadget<CompressH, ConstraintF>>::OutputVar;
    type LeafHash = LeafHG;
    type TwoToOneHash = CompressHG;
}

type JubJubMerkleTree = MT<JubJubMerkleTreeParams>;

type InnerDigest =
<CompressHG as TwoToOneCRHSchemeGadget<CompressH, ConstraintF>>::OutputVar;


/// Generate a merkle tree, its constraints, and test its constraints
fn merkle_tree_test(
    leaves: &[Vec<u8>],
    use_bad_root: bool,
    update_query: Option<(usize, Vec<u8>)>,
) -> () {
    let mut rng = ark_std::test_rng();

    let leaf_crh_params = <LeafH as CRHScheme>::setup(&mut rng).unwrap();
    let l_c_p = leaf_crh_params.clone();
    let two_to_one_crh_params = <CompressH as TwoToOneCRHScheme>::setup(&mut rng).unwrap();
    let t_o_p = two_to_one_crh_params.clone();
    let mut tree =
        JubJubMerkleTree::new(&leaf_crh_params, &two_to_one_crh_params, leaves).unwrap();
    let c = JubJubMerkleTree::new(&leaf_crh_params, &two_to_one_crh_params, leaves).unwrap();
    let root = tree.root();
    for (i, leaf) in leaves.iter().enumerate() {
        let cs = ConstraintSystem::<Fq>::new_ref();
        let proof = tree.generate_proof(i).unwrap();
        assert!(proof
            .verify(
                &leaf_crh_params,
                &two_to_one_crh_params,
                &root,
                leaf.as_slice()
            )
            .unwrap());

        // Allocate Merkle Tree Root
        let root = <LeafHG as CRHSchemeGadget<LeafH, _>>::OutputVar::new_witness(
            ark_relations::ns!(cs, "new_digest"),
            || {
                if use_bad_root {
                    Ok(<LeafH as CRHScheme>::Output::default())
                } else {
                    Ok(root)
                }
            },
        )
            .unwrap();

        let constraints_from_digest = cs.num_constraints();
        println!("constraints from digest: {}", constraints_from_digest);

        // Allocate Parameters for CRH
        let leaf_crh_params_var =
            <LeafHG as CRHSchemeGadget<LeafH, _>>::ParametersVar::new_constant(
                ark_relations::ns!(cs, "leaf_crh_parameter"),
                &leaf_crh_params,
            )
                .unwrap();
        let two_to_one_crh_params_var =
            <CompressHG as TwoToOneCRHSchemeGadget<CompressH, _>>::ParametersVar::new_constant(
                ark_relations::ns!(cs, "two_to_one_crh_parameter"),
                &two_to_one_crh_params,
            )
                .unwrap();

        let constraints_from_params = cs.num_constraints() - constraints_from_digest;
        println!("constraints from parameters: {}", constraints_from_params);

        // Allocate Leaf
        let leaf_g = UInt8::new_input_vec(cs.clone(), leaf).unwrap();

        let constraints_from_leaf =
            cs.num_constraints() - constraints_from_params - constraints_from_digest;
        println!("constraints from leaf: {}", constraints_from_leaf);

        // Allocate Merkle Tree Path
        let cw: PathVar<JubJubMerkleTreeParams, Fq, JubJubMerkleTreeParamsVar> =
            PathVar::new_witness(ark_relations::ns!(cs, "new_witness"), || Ok(&proof)).unwrap();

        let constraints_from_path = cs.num_constraints()
            - constraints_from_params
            - constraints_from_digest
            - constraints_from_leaf;
        println!("constraints from path: {}", constraints_from_path);

        assert!(cs.is_satisfied().unwrap());
        assert!(cw
            .verify_membership(
                &leaf_crh_params_var,
                &two_to_one_crh_params_var,
                &root,
                &leaf_g,
            )
            .unwrap()
            .value()
            .unwrap());
        let setup_constraints = constraints_from_leaf
            + constraints_from_digest
            + constraints_from_params
            + constraints_from_path;
        println!(
            "number of constraints: {}",
            cs.num_constraints() - setup_constraints
        );

        assert!(
            cs.is_satisfied().unwrap(),
            "verification constraints not satisfied"
        );

        let c = JubJubMerkleTreeCircuit::new(&l_c_p,&t_o_p,leaf.clone(),tree.root(),proof).unwrap();

        let mut rng = StdRng::seed_from_u64(0u64);
        let (pk, vk) = {
            ark_groth16::Groth16::<Bls12_381>::circuit_specific_setup(c.clone(), &mut rng).unwrap()
        };

        let pvk = ark_groth16::prepare_verifying_key(&vk);

        // all input are witnesses no public input 
        // TODO: fix this
        let public_input = [];

        let groth_proof = ark_groth16::Groth16::<Bls12_381>::create_random_proof_with_reduction(c,&pk,&mut rng).unwrap();

        
        let a = ark_groth16::Groth16::<Bls12_381>::verify_proof(&pvk,&groth_proof,&public_input).unwrap();

        assert!(a);

        println!("verification result: {}",a);

        break;

    }

}

#[test]
fn good_root_test() {
    let mut leaves = Vec::new();
    for i in 0..4u8 {
        let input = vec![i; 30];
        leaves.push(input);
    }
    merkle_tree_test(&leaves, false, Some((3usize, vec![7u8; 30])));
}

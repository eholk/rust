use crate::iter::Iterator;
use crate::ops::{Generator, GeneratorState};
use crate::pin::Pin;

// A blanket implementation that enables using generators as iterators.

#[allow(ineffective_unstable_trait_impl)]
#[unstable(feature = "generator_trait", issue = "43122")]
impl<G, I> Iterator for Pin<&mut G>
where
    G: Generator<(), Yield = I, Return = ()>,
{
    type Item = I;

    fn next(&mut self) -> Option<Self::Item> {
        match self.as_mut().resume(()) {
            GeneratorState::Yielded(i) => Some(i),
            GeneratorState::Complete(()) => None,
        }
    }
}

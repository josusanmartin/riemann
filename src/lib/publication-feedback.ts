export const publicationMismatchMessage = "The proof passed verification. Publication was blocked because the worker and publisher verifier fingerprints differ. Contact the maintainers with your job ID before submitting again.";

export const nanodaMismatchMessage = "The proof passed on the worker, but its receipt names a different checker from the pinned nanoda release. Contact the maintainers with your job ID before submitting again.";

export function isPublicationMismatch(message: string | null | undefined) {
  return message === publicationMismatchMessage || message === nanodaMismatchMessage ||
    message === "Verifier template is stale; rebuild the pinned E2B template before accepting submissions";
}

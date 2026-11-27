export const publicationMismatchMessage = "The proof passed verification. Publication was blocked because the worker and publisher verifier fingerprints differ. Contact the maintainers with your job ID before submitting again.";

export function isPublicationMismatch(message: string | null | undefined) {
  return message === publicationMismatchMessage ||
    message === "Verifier template is stale; rebuild the pinned E2B template before accepting submissions";
}

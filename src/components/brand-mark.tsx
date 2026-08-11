export function BrandMark({ className = "" }: { className?: string }) {
  return (
    <svg
      aria-hidden="true"
      className={className}
      viewBox="0 0 42 42"
      fill="none"
    >
      <rect x="1" y="1" width="40" height="40" rx="12" fill="currentColor" />
      <path
        d="M12 12.5h18L18.5 21 30 29.5H12"
        stroke="var(--brand-mark-ink, #153e35)"
        strokeWidth="3.2"
        strokeLinecap="round"
        strokeLinejoin="round"
      />
      <circle cx="30.5" cy="11.5" r="2.25" fill="var(--brand-dot, #ff7557)" />
    </svg>
  );
}

export function CodeBlock({ children, label }: { children: string; label?: string }) {
  return (
    <div className="code-block">
      {label && <div className="code-label">{label}</div>}
      <pre><code>{children}</code></pre>
    </div>
  );
}

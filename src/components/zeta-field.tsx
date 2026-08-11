export function ZetaField() {
  return (
    <svg
      className="zeta-field"
      viewBox="0 0 720 560"
      fill="none"
      aria-hidden="true"
      preserveAspectRatio="xMidYMid slice"
    >
      <defs>
        <linearGradient id="curve" x1="50" y1="500" x2="650" y2="40" gradientUnits="userSpaceOnUse">
          <stop stopColor="#d7f58b" stopOpacity="0.08" />
          <stop offset="0.5" stopColor="#d7f58b" stopOpacity="0.72" />
          <stop offset="1" stopColor="#ff7557" stopOpacity="0.22" />
        </linearGradient>
        <radialGradient id="glow">
          <stop stopColor="#d7f58b" stopOpacity="0.7" />
          <stop offset="1" stopColor="#d7f58b" stopOpacity="0" />
        </radialGradient>
      </defs>
      {Array.from({ length: 11 }, (_, index) => (
        <path
          key={index}
          d={`M ${-70 + index * 36} 590 C ${100 + index * 19} 415, ${110 + index * 22} 265, ${310 + index * 13} 260 S ${550 + index * 10} 190, ${690 + index * 6} -40`}
          stroke="url(#curve)"
          strokeWidth={index === 5 ? 2.4 : 1}
          opacity={0.22 + index * 0.045}
        />
      ))}
      <line x1="370" y1="40" x2="370" y2="520" stroke="#d7f58b" strokeOpacity="0.24" strokeDasharray="3 7" />
      {[88, 148, 218, 294, 378, 466].map((y, index) => (
        <g key={y}>
          <circle cx="370" cy={y} r="28" fill="url(#glow)" opacity={0.34 + index * 0.05} />
          <circle cx="370" cy={y} r={index === 3 ? 5 : 3.2} fill={index === 3 ? "#ff7557" : "#d7f58b"} />
        </g>
      ))}
      <text x="386" y="54" fill="#d7f58b" fillOpacity="0.55" fontSize="12" fontFamily="monospace">Re(s) = 1/2</text>
    </svg>
  );
}

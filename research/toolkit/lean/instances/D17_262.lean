import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 262 of the cap-17 certificate: slots 134144 .. 134655 -/
theorem chk_262 : chunkCheck 17 T stdSt 134144 512 = true := by decide +kernel

end Row17

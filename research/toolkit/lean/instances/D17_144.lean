import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 144 of the cap-17 certificate: slots 73728 .. 74239 -/
theorem chk_144 : chunkCheck 17 T stdSt 73728 512 = true := by decide +kernel

end Row17

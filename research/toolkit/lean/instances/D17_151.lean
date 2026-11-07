import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 151 of the cap-17 certificate: slots 77312 .. 77823 -/
theorem chk_151 : chunkCheck 17 T stdSt 77312 512 = true := by decide +kernel

end Row17

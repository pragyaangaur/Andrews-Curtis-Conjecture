import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 192 of the cap-17 certificate: slots 98304 .. 98815 -/
theorem chk_192 : chunkCheck 17 T stdSt 98304 512 = true := by decide +kernel

end Row17

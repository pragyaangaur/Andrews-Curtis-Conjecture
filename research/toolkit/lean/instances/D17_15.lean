import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 15 of the cap-17 certificate: slots 7680 .. 8191 -/
theorem chk_15 : chunkCheck 17 T stdSt 7680 512 = true := by decide +kernel

end Row17

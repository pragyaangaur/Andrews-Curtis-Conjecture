import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 121 of the cap-17 certificate: slots 61952 .. 62463 -/
theorem chk_121 : chunkCheck 17 T stdSt 61952 512 = true := by decide +kernel

end Row17

import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 352 of the cap-17 certificate: slots 180224 .. 180735 -/
theorem chk_352 : chunkCheck 17 T stdSt 180224 512 = true := by decide +kernel

end Row17

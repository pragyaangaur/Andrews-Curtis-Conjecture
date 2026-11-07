import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 222 of the cap-17 certificate: slots 113664 .. 114175 -/
theorem chk_222 : chunkCheck 17 T stdSt 113664 512 = true := by decide +kernel

end Row17

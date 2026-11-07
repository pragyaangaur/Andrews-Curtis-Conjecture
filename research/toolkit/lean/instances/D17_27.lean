import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 27 of the cap-17 certificate: slots 13824 .. 14335 -/
theorem chk_27 : chunkCheck 17 T stdSt 13824 512 = true := by decide +kernel

end Row17

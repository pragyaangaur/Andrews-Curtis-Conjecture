import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 402 of the cap-17 certificate: slots 205824 .. 206335 -/
theorem chk_402 : chunkCheck 17 T stdSt 205824 512 = true := by decide +kernel

end Row17

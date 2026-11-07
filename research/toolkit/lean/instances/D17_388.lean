import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 388 of the cap-17 certificate: slots 198656 .. 199167 -/
theorem chk_388 : chunkCheck 17 T stdSt 198656 512 = true := by decide +kernel

end Row17

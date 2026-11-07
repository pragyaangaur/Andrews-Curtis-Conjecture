import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 406 of the cap-17 certificate: slots 207872 .. 208383 -/
theorem chk_406 : chunkCheck 17 T stdSt 207872 512 = true := by decide +kernel

end Row17

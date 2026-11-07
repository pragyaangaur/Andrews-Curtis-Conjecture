import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 43 of the cap-17 certificate: slots 22016 .. 22527 -/
theorem chk_43 : chunkCheck 17 T stdSt 22016 512 = true := by decide +kernel

end Row17

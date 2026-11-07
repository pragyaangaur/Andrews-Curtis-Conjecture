import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 255 of the cap-17 certificate: slots 130560 .. 131071 -/
theorem chk_255 : chunkCheck 17 T stdSt 130560 512 = true := by decide +kernel

end Row17

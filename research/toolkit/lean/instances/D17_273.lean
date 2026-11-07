import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 273 of the cap-17 certificate: slots 139776 .. 140287 -/
theorem chk_273 : chunkCheck 17 T stdSt 139776 512 = true := by decide +kernel

end Row17

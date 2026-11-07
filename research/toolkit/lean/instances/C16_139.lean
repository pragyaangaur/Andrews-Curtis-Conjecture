import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 139 of the cap-16 certificate: slots 142336 .. 143359 -/
theorem chk_139 : chunkCheck 16 T stdSt 142336 1024 = true := by decide +kernel

end Row16

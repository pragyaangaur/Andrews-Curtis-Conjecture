import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 172 of the cap-16 certificate: slots 176128 .. 177151 -/
theorem chk_172 : chunkCheck 16 T stdSt 176128 1024 = true := by decide +kernel

end Row16

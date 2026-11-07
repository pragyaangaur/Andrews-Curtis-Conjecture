import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 63 of the cap-16 certificate: slots 64512 .. 65535 -/
theorem chk_63 : chunkCheck 16 T stdSt 64512 1024 = true := by decide +kernel

end Row16

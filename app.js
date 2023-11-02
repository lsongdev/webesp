import { ready } from 'https://lsong.org/scripts/dom.js';
import { readAsBinaryString } from 'https://lsong.org/scripts/file.js';
import { requestPort } from 'https://lsong.org/scripts/serialport.js';
import { ESPLoader, Transport } from './esptool.min.js';

ready(() => {
  const connect = document.getElementById('connect');
  const baudrate = document.getElementById('baudrate');
  const flash = document.getElementById('flash');
  const erase = document.getElementById('erase');
  const output = document.getElementById('output');
  const status = document.getElementById('status');
  const board = document.getElementById('device');
  const progressBar = document.querySelector('progress-bar');
  const fileList = document.getElementById('file-list');
  const addFileButton = document.getElementById('add-file');
  const eraseAllCheckbox = document.getElementById('erase-all');
  const compressCheckbox = document.getElementById('compress');

  // File management functions
  function createFileEntry() {
    const entry = document.createElement('div');
    entry.className = 'file-entry';
    entry.innerHTML = `
      <input type="text" class="address-input" value="0x00" placeholder="Flash address">
      <input type="file" class="file-input">
      <button class="remove-file">-</button>
    `;
    
    const removeButton = entry.querySelector('.remove-file');
    removeButton.addEventListener('click', () => {
      if (fileList.children.length > 1) {
        entry.remove();
      }
    });
    
    // Show remove button only if there's more than one file entry
    const updateRemoveButtons = () => {
      document.querySelectorAll('.remove-file').forEach(btn => {
        btn.style.display = fileList.children.length > 1 ? 'inline' : 'none';
      });
    };
    
    fileList.appendChild(entry);
    updateRemoveButtons();
  }

  addFileButton.addEventListener('click', createFileEntry);

  const terminal = {
    clean: () => output.value = '',
    write: data => output.value += data,
    writeLine: data => {
      output.value += data + '\n'
      output.scrollTop = output.scrollHeight;
    },
  };

  var loader;
  connect.addEventListener('click', async () => {
    const device = await requestPort();
    const transport = new Transport(device);
    status.textContent = await transport.get_info();
    const loaderOptions = {
      baudrate: +baudrate.value,
      transport,
      terminal,
    };
    loader = new ESPLoader(loaderOptions);
    const chip = await loader.main_fn();
    board.textContent = chip;
  });

  erase.addEventListener('click', async () => {
    await loader.erase_flash();
  });

  flash.addEventListener('click', async () => {
    const entries = fileList.querySelectorAll('.file-entry');
    const fileArray = [];

    for (const entry of entries) {
      const fileInput = entry.querySelector('.file-input');
      const addressInput = entry.querySelector('.address-input');
      
      const file = fileInput.files[0];
      if (!file) {
        terminal.writeLine('Not all files are selected');
        return;
      }

      const data = await readAsBinaryString(file);
      fileArray.push({
        data,
        address: parseInt(addressInput.value)
      });
    }
    // console.log(fileArray);
    if (fileArray.length === 0) {
      terminal.writeLine('No files to flash');
      return;
    }
    const flashOptions = {
      fileArray,
      flashSize: "keep",
      eraseAll: eraseAllCheckbox.checked,
      compress: compressCheckbox.checked,
      reportProgress: (index, written, total) => {
        progressBar.value = (written / total) * 100;
      },
      calculateMD5Hash: image =>
        CryptoJS.MD5(CryptoJS.enc.Latin1.parse(image)).toString(),
    };
    if (!loader) {
      terminal.writeLine('Connect to a device first');
      return;
    }
    try {
      await loader.write_flash(flashOptions);
      console.log('Flash complete');
      await loader.hard_reset();
    } catch (error) {
      console.error('Flash failed:', error);
      terminal.writeLine('Flash failed: ' + error.message);
    }
  });
});

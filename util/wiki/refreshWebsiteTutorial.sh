#!/usr/bin/env bash

if [ -d "vercors-web" ]; then
  # Control will enter here if $DIRECTORY exists.
  echo "vercors-web already exists. The script pulls it by default and then deletes it, so to prevent loss of work the script will exit now."
  exit 1
fi

git clone https://github.com/utwente-fmt/vercors-web.git
echo "Running generate_wiki_pdf.py"
python3 generate_wiki_pdf.py \
        -w vercors-web/views/site/_wiki_content.php \
        -m vercors-web/views/site/_wiki_menu.php
cd vercors-web.git
git commit -am "Update website tutorial from github wiki"
git push
cd ..
rm -rf vercors-web

echo "vercors-web updated, don't forget to also deploy it!"

# get certificate manually
# echo | openssl s_client -connect 130.89.1.50:443 | openssl x509 -out ./curlftpcert.pem

# mount
# curlftpfs -o ssl,cacert=./curlftpcert.pem,no_verify_peer,user=u869582 webservice.utwente.nl ./ftpmnt/

# umount ftpmnt
# rm curlftpcert.pem
